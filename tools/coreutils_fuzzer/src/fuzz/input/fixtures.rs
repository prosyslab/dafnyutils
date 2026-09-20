use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, SymlinkSpec};
use std::path::PathBuf;

pub(super) fn basic_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"beta\n".to_vec(),
                mode: 0o600,
            },
            FileSpec {
                relative_path: PathBuf::from("target.txt"),
                bytes: b"target\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("a-link"),
            target: PathBuf::from("a.txt"),
        }],
        hardlinks: Vec::new(),
    }
}

pub(super) fn line_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"one\n\nthree\nfour\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("left.txt"),
                bytes: b"apple\nbanana\nbanana\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right.txt"),
                bytes: b"banana\ncarrot\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("dups.txt"),
                bytes: b"a\na\nb\nc\nc\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("case.txt"),
                bytes: b"A\na\nB\nb\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("empty.txt"),
                bytes: Vec::new(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("payload.bin"),
                bytes: vec![0, 1, 2, 3, b'\n'],
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("target.txt"),
                bytes: b"existing target\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("a-link"),
            target: PathBuf::from("a.txt"),
        }],
        hardlinks: Vec::new(),
    }
}
