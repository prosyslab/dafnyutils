use super::GeneratedCase;
use rand::rngs::StdRng;
use rand::Rng;
use std::collections::VecDeque;

const DEFAULT_MAX_CASES: usize = 128;

#[derive(Debug, Clone)]
pub(crate) struct InterestingCorpus {
    max_cases: usize,
    cases: VecDeque<GeneratedCase>,
}

impl Default for InterestingCorpus {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_CASES)
    }
}

impl InterestingCorpus {
    pub(crate) fn new(max_cases: usize) -> Self {
        Self {
            max_cases: max_cases.max(1),
            cases: VecDeque::new(),
        }
    }

    pub(crate) fn maybe_add(&mut self, case: &GeneratedCase, interesting: bool) {
        if !interesting {
            return;
        }
        if self.cases.len() >= self.max_cases {
            self.cases.pop_front();
        }
        self.cases.push_back(case.clone());
    }

    pub(crate) fn choose(&self, rng: &mut StdRng) -> Option<GeneratedCase> {
        if self.cases.is_empty() {
            return None;
        }
        let idx = rng.random_range(0..self.cases.len());
        self.cases.get(idx).cloned()
    }
}
