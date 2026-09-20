use serde::{de::Error as _, Deserialize, Deserializer, Serialize};
use std::process::ExitStatus;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum Termination {
    Exit {
        code: i32,
        raw_status: i32,
    },
    Signal {
        signal: i32,
        core_dumped: bool,
        raw_status: i32,
    },
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum TerminationWire {
    Exit {
        code: i32,
        raw_status: i32,
    },
    Signal {
        signal: i32,
        core_dumped: bool,
        raw_status: i32,
    },
}

impl<'de> Deserialize<'de> for Termination {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let outcome = match TerminationWire::deserialize(deserializer)? {
            TerminationWire::Exit { code, raw_status } => Self::Exit { code, raw_status },
            TerminationWire::Signal {
                signal,
                core_dumped,
                raw_status,
            } => Self::Signal {
                signal,
                core_dumped,
                raw_status,
            },
        };
        outcome.validate().map_err(D::Error::custom)?;
        Ok(outcome)
    }
}

impl Termination {
    #[cfg(test)]
    pub(crate) fn test_exit(code: i32) -> Self {
        #[cfg(unix)]
        let raw_status = code << 8;
        #[cfg(not(unix))]
        let raw_status = code;
        Self::Exit { code, raw_status }
    }

    pub(crate) fn from_status(status: ExitStatus) -> Self {
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            let raw_status = status.into_raw();
            if let Some(code) = status.code() {
                Self::Exit { code, raw_status }
            } else {
                Self::Signal {
                    signal: status
                        .signal()
                        .expect("reaped Unix status is exit or signal"),
                    core_dumped: status.core_dumped(),
                    raw_status,
                }
            }
        }
        #[cfg(not(unix))]
        {
            let code = status.code().unwrap_or(1);
            Self::Exit {
                code,
                raw_status: code,
            }
        }
    }

    pub(crate) fn exit_code(self) -> Option<i32> {
        match self {
            Self::Exit { code, .. } => Some(code),
            Self::Signal { .. } => None,
        }
    }

    pub(crate) fn is_success(self) -> bool {
        self.exit_code() == Some(0)
    }

    fn validate(self) -> Result<(), String> {
        #[cfg(unix)]
        {
            match self {
                Self::Exit { code, raw_status }
                    if (0..=255).contains(&code) && raw_status == code << 8 =>
                {
                    Ok(())
                }
                Self::Exit { code, raw_status } => Err(format!(
                    "exit code {code} disagrees with raw Unix wait status {raw_status}"
                )),
                Self::Signal {
                    signal,
                    core_dumped,
                    raw_status,
                } if (1..=127).contains(&signal)
                    && signal != 127
                    && raw_status == signal | if core_dumped { 128 } else { 0 } =>
                {
                    Ok(())
                }
                Self::Signal {
                    signal,
                    core_dumped,
                    raw_status,
                } => Err(format!(
                    "signal {signal} core_dumped={core_dumped} disagrees with raw Unix wait status {raw_status}"
                )),
            }
        }
        #[cfg(not(unix))]
        {
            match self {
                Self::Exit { code, raw_status } if code == raw_status => Ok(()),
                Self::Exit { code, raw_status } => Err(format!(
                    "exit code {code} disagrees with platform status {raw_status}"
                )),
                Self::Signal { .. } => {
                    Err("signal outcomes are unsupported on this platform".to_string())
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Termination;
    use std::process::Command;

    // A normal exit whose conventional shell number is 141 remains a normal exit.
    #[test]
    #[cfg(unix)]
    fn process_outcome_preserves_actual_exit_141() {
        let status = Command::new("/bin/sh")
            .args(["-c", "exit 141"])
            .status()
            .unwrap();
        assert_eq!(
            Termination::from_status(status),
            Termination::Exit {
                code: 141,
                raw_status: 141 << 8
            }
        );
    }

    // A real SIGPIPE termination retains signal provenance and cannot equal exit 141.
    #[test]
    #[cfg(unix)]
    fn process_outcome_preserves_actual_sigpipe() {
        let status = Command::new("/bin/sh")
            .args(["-c", "kill -PIPE $$"])
            .status()
            .unwrap();
        assert_eq!(
            Termination::from_status(status),
            Termination::Signal {
                signal: 13,
                core_dumped: false,
                raw_status: 13
            }
        );
    }

    // A typed payload cannot pair a normal exit with a signal-shaped raw wait status.
    #[test]
    fn process_outcome_rejects_inconsistent_raw_status() {
        let error =
            serde_json::from_str::<Termination>(r#"{"kind":"exit","code":141,"raw_status":13}"#)
                .unwrap_err();
        assert!(error.to_string().contains("disagrees"), "{error}");
    }

    // Unknown fields cannot silently widen a current typed process outcome.
    #[test]
    fn process_outcome_rejects_unknown_fields() {
        assert!(serde_json::from_str::<Termination>(
            r#"{"kind":"signal","signal":13,"core_dumped":false,"raw_status":13,"code":141}"#
        )
        .is_err());
    }
}
