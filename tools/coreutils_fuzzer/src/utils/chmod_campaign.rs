use std::collections::BTreeMap;

const CONTROLLED_CHMOD_UMASKS: [u32; 5] = [0o000, 0o005, 0o022, 0o027, 0o077];
const CONTROLLED_PATH: &str = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin";

pub fn selected_chmod_umask(seed: u64, iteration: usize) -> u32 {
    CONTROLLED_CHMOD_UMASKS[(seed as usize).wrapping_add(iteration) % CONTROLLED_CHMOD_UMASKS.len()]
}

pub fn validate_process_umask(umask: u32) -> Result<(), String> {
    if umask > 0o777 {
        return Err(format!("process umask is out of range: {umask:04o}"));
    }
    Ok(())
}

#[cfg(target_os = "linux")]
pub fn current_process_umask() -> Result<u32, String> {
    let status = std::fs::read_to_string("/proc/self/status")
        .map_err(|error| format!("failed to read process umask from /proc/self/status: {error}"))?;
    let value = status
        .lines()
        .find_map(|line| line.strip_prefix("Umask:").map(str::trim))
        .ok_or_else(|| "process status does not contain Umask".to_string())?;
    let umask = u32::from_str_radix(value, 8)
        .map_err(|_| format!("process status contains invalid Umask `{value}`"))?;
    validate_process_umask(umask)?;
    Ok(umask)
}

#[cfg(not(target_os = "linux"))]
pub fn current_process_umask() -> Result<u32, String> {
    Err(
        "capturing a process umask without process-global mutation requires Linux /proc"
            .to_string(),
    )
}

pub fn canonical_environment_config(umask: u32) -> Result<BTreeMap<String, String>, String> {
    if !CONTROLLED_CHMOD_UMASKS.contains(&umask) {
        return Err(format!("unsupported controlled chmod umask {umask:04o}"));
    }
    Ok(canonical_process_environment())
}

pub fn canonical_process_environment() -> BTreeMap<String, String> {
    BTreeMap::from([
        ("LANG".to_string(), "C".to_string()),
        ("LC_ALL".to_string(), "C".to_string()),
        ("PATH".to_string(), CONTROLLED_PATH.to_string()),
        ("QUOTING_STYLE".to_string(), "literal".to_string()),
        ("TERM".to_string(), "dumb".to_string()),
        ("TZ".to_string(), "UTC0".to_string()),
    ])
}

#[cfg(test)]
mod tests {
    use super::{
        canonical_environment_config, canonical_process_environment, selected_chmod_umask,
    };

    // Seed and iteration choose only an approved umask, deterministically.
    #[test]
    fn controlled_chmod_umask_selection_is_fixed_and_deterministic() {
        let selected = selected_chmod_umask(3, 9);

        assert_eq!(selected, selected_chmod_umask(3, 9));
        assert!([0o000, 0o005, 0o022, 0o027, 0o077].contains(&selected));
    }

    // The implementation campaign rejects unapproved umasks before spawning chmod.
    #[test]
    fn controlled_chmod_environment_rejects_unknown_umask() {
        assert!(canonical_environment_config(0o777).is_err());
    }

    // Every target receives one explicit, secret-free environment map.
    #[test]
    fn controlled_environment_is_complete_and_secret_free() {
        assert_eq!(
            canonical_process_environment()
                .keys()
                .cloned()
                .collect::<Vec<_>>(),
            ["LANG", "LC_ALL", "PATH", "QUOTING_STYLE", "TERM", "TZ"]
        );
    }
}
