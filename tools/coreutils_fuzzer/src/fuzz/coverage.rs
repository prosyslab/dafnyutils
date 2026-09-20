use std::collections::{BTreeSet, HashSet};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct OptionCoverage {
    pool: BTreeSet<String>,
    seen_single: BTreeSet<String>,
    seen_pairs: BTreeSet<(String, String)>,
}

impl OptionCoverage {
    pub(crate) fn new(option_pool: &[String]) -> Self {
        Self {
            pool: option_pool.iter().cloned().collect(),
            ..Self::default()
        }
    }

    pub(crate) fn observe_case(&mut self, argv: &[String]) {
        let used = extract_used_options(argv, &self.pool);
        for opt in &used {
            self.seen_single.insert(opt.clone());
        }
        for_each_unordered_pair(&used, |left, right| {
            self.seen_pairs.insert((left.clone(), right.clone()));
        });
    }

    pub(crate) fn render_report(&self) -> String {
        let total_single = self.pool.len();
        let total_pairs = all_pool_pairs(&self.pool).len();
        let single_cov = coverage_percent(self.seen_single.len(), total_single);
        let pair_cov = coverage_percent(self.seen_pairs.len(), total_pairs);
        format!(
            "Option coverage: singles {}/{} ({:.1}%), pairs {}/{} ({:.1}%)",
            self.seen_single.len(),
            total_single,
            single_cov,
            self.seen_pairs.len(),
            total_pairs,
            pair_cov
        )
    }

    pub(crate) fn counts(&self) -> (usize, usize, usize, usize) {
        (
            self.seen_single.len(),
            self.pool.len(),
            self.seen_pairs.len(),
            all_pool_pairs(&self.pool).len(),
        )
    }
}

pub(crate) fn extract_used_options(argv: &[String], pool: &BTreeSet<String>) -> Vec<String> {
    let mut unique = HashSet::new();
    for arg in argv {
        if pool.contains(arg) {
            unique.insert(arg.clone());
            continue;
        }
        if let Some((prefix, _)) = arg.split_once('=') {
            if pool.contains(prefix) {
                unique.insert(prefix.to_string());
            }
        }
    }
    let mut used: Vec<String> = unique.into_iter().collect();
    used.sort();
    used
}

fn all_pool_pairs(pool: &BTreeSet<String>) -> BTreeSet<(String, String)> {
    let options: Vec<String> = pool.iter().cloned().collect();
    let mut pairs = BTreeSet::new();
    for_each_unordered_pair(&options, |left, right| {
        pairs.insert((left.clone(), right.clone()));
    });
    pairs
}

fn for_each_unordered_pair<T>(items: &[T], mut f: impl FnMut(&T, &T)) {
    for i in 0..items.len() {
        for j in (i + 1)..items.len() {
            f(&items[i], &items[j]);
        }
    }
}

fn coverage_percent(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        100.0
    } else {
        (numerator as f64 * 100.0) / denominator as f64
    }
}
