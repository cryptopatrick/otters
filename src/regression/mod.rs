//! Helpers for working with the legacy Otter example suite.

mod executor;

use std::ffi::OsStr;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub use executor::{
    ProverMetrics, RegressionExecutor, RegressionGroupSummary, RegressionResult,
    RegressionSummary,
};

/// A single example identified by its `.in` input and optional expected output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExampleCase {
    pub input: PathBuf,
    pub expected_output: Option<PathBuf>,
}

impl ExampleCase {
    pub fn name(&self) -> Option<&OsStr> {
        self.input.file_name()
    }

    pub fn load_input(&self) -> io::Result<String> {
        fs::read_to_string(&self.input)
    }

    pub fn load_expected_output(&self) -> io::Result<Option<String>> {
        match &self.expected_output {
            Some(path) => fs::read_to_string(path).map(Some),
            None => Ok(None),
        }
    }
}

/// Represents the curated collection of regression examples bundled with Otter.
#[derive(Clone, Debug)]
pub struct ExampleSuite {
    root: PathBuf,
}

impl Default for ExampleSuite {
    fn default() -> Self {
        Self::new(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("_wb")
                .join("otter-examples"),
        )
    }
}

impl ExampleSuite {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn available_inputs(&self) -> io::Result<Vec<PathBuf>> {
        self.collect_with_extension("in")
    }

    pub fn available_outputs(&self) -> io::Result<Vec<PathBuf>> {
        self.collect_with_extension("out")
    }

    pub fn available_cases(&self) -> io::Result<Vec<ExampleCase>> {
        let inputs = self.available_inputs()?;
        let outputs = self.available_outputs()?;
        let mut by_stem: std::collections::HashMap<String, PathBuf> = outputs
            .into_iter()
            .filter_map(|path| {
                Some((path.file_stem()?.to_string_lossy().to_string(), path))
            })
            .collect();

        let mut cases = Vec::new();
        for input in inputs {
            let stem = match input.file_stem() {
                Some(stem) => stem.to_string_lossy().to_string(),
                None => continue,
            };
            let expected_output = by_stem.remove(&stem);
            cases.push(ExampleCase { input, expected_output });
        }
        cases.sort_by(|a, b| a.input.cmp(&b.input));
        Ok(cases)
    }

    fn collect_with_extension(&self, ext: &str) -> io::Result<Vec<PathBuf>> {
        let mut paths = Vec::new();
        self.walk(&self.root, ext, &mut paths)?;
        paths.sort();
        Ok(paths)
    }

    fn walk(
        &self,
        dir: &Path,
        ext: &str,
        acc: &mut Vec<PathBuf>,
    ) -> io::Result<()> {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                self.walk(&path, ext, acc)?;
            } else if path.extension().and_then(OsStr::to_str) == Some(ext) {
                acc.push(path);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{ExampleSuite, RegressionExecutor};

    #[test]
    fn enumerate_examples() {
        let suite = ExampleSuite::default();
        let inputs = suite.available_inputs().expect("scan inputs");
        assert!(!inputs.is_empty(), "expected at least one input example");
        let cases = suite.available_cases().expect("cases lookup");
        assert!(!cases.is_empty());
        let first = &cases[0];
        let input = first.load_input().expect("read input");
        assert!(!input.is_empty());
        if let Some(expected) =
            first.load_expected_output().expect("read output")
        {
            assert!(!expected.is_empty());
        }
    }

    #[test]
    fn regression_executor_groups_cases() {
        let suite = ExampleSuite::default();
        let executor = RegressionExecutor::new(suite);
        let groups = executor.group_cases();
        assert!(!groups.is_empty());
    }
}
