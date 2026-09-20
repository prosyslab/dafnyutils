use std::path::Path;

pub(crate) fn format_path_error(action: &str, path: &Path, err: impl std::fmt::Display) -> String {
    format!("failed to {action} `{}`: {err}", path.display())
}

pub(crate) fn sanitize_util_name(util: &str) -> String {
    util.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '-' || ch == '_' {
                ch
            } else {
                '-'
            }
        })
        .collect()
}
