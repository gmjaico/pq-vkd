//! Multilinear polynomials in coefficient form and the folding
//! helpers for the PCS which the prover and verifier share

use ark_ff::{Field as _, One, Zero};
use rayon::prelude::*;

use crate::{Error, Field, Parameters, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultilinearPolynomial {
    coefficients: Vec<Field>,
}

impl MultilinearPolynomial {
    pub fn new(coefficients: Vec<Field>) -> Result<Self> {
        if coefficients.is_empty() || !coefficients.len().is_power_of_two() {
            return Err(Error::InvalidParameters(
                "multilinear coefficients must have non-empty power-of-two length",
            ));
        }
        Parameters::new(coefficients.len().ilog2() as usize)?;
        Ok(Self { coefficients })
    }

    /// turns the table of values on {0,1}^n (Value/Randomizer
    /// entries) into coefficientsm, slot bit i is variable i
    pub fn from_boolean_evaluations(evaluations: Vec<Field>) -> Result<Self> {
        if evaluations.is_empty() || !evaluations.len().is_power_of_two() {
            return Err(Error::InvalidParameters(
                "Boolean evaluations must have non-empty power-of-two length",
            ));
        }
        Parameters::new(evaluations.len().ilog2() as usize)?;
        let mut coefficients = evaluations;
        for variable in 0..coefficients.len().ilog2() as usize {
            let bit = 1usize << variable;
            for index in 0..coefficients.len() {
                if index & bit != 0 {
                    let lower = coefficients[index ^ bit];
                    coefficients[index] -= lower;
                }
            }
        }
        Self::new(coefficients)
    }

    pub fn to_boolean_evaluations(&self) -> Vec<Field> {
        let mut evaluations = self.coefficients.clone();
        for variable in 0..self.num_vars() {
            let bit = 1usize << variable;
            for index in 0..evaluations.len() {
                if index & bit != 0 {
                    let lower = evaluations[index ^ bit];
                    evaluations[index] += lower;
                }
            }
        }
        evaluations
    }

    pub fn zero(num_vars: usize) -> Result<Self> {
        Parameters::new(num_vars)?;
        Self::new(vec![Field::zero(); 1usize << num_vars])
    }

    pub fn num_vars(&self) -> usize {
        self.coefficients.len().ilog2() as usize
    }

    pub fn coefficients(&self) -> &[Field] {
        &self.coefficients
    }

    pub fn evaluate(&self, point: &[Field]) -> Result<Field> {
        if point.len() != self.num_vars() {
            return Err(Error::InvalidParameters(
                "evaluation point has the wrong dimension",
            ));
        }
        if let Some(slot) = boolean_slot(point) {
            return Ok(self.evaluate_at_slot(slot));
        }
        let mut coefficients = self.coefficients.clone();
        for challenge in point {
            coefficients = fold_coefficients(&coefficients, *challenge);
        }
        Ok(coefficients[0])
    }

    pub fn evaluate_at_slot(&self, slot: usize) -> Field {
        debug_assert!(slot < self.coefficients.len());
        let mut sum = Field::zero();
        let mut submask = slot;
        loop {
            sum += self.coefficients[submask];
            if submask == 0 {
                return sum;
            }
            submask = (submask - 1) & slot;
        }
    }

    /// f(a, a^2, a^4, ...), same as reading the coefficients
    /// as one univariate polynomial and evaluating it at a
    pub fn twin_evaluate(&self, point: Field) -> Field {
        evaluate_univariate(&self.coefficients, point)
    }
}

/// returns the slot index if every coordinate of point is 0 or 1
fn boolean_slot(point: &[Field]) -> Option<usize> {
    point
        .iter()
        .enumerate()
        .try_fold(0usize, |slot, (variable, coordinate)| {
            if coordinate.is_zero() {
                Some(slot)
            } else if coordinate.is_one() {
                Some(slot | (1usize << variable))
            } else {
                None
            }
        })
}

pub fn fold_coefficients(coefficients: &[Field], challenge: Field) -> Vec<Field> {
    if coefficients.len() == 1 {
        return coefficients.to_vec();
    }
    coefficients
        .chunks_exact(2)
        .map(|pair| pair[0] + challenge * pair[1])
        .collect()
}

pub fn evaluate_univariate(coefficients: &[Field], point: Field) -> Field {
    coefficients
        .iter()
        .rev()
        .fold(Field::zero(), |acc, coefficient| acc * point + coefficient)
}

pub fn evaluate_multilinear(coefficients: &[Field], point: &[Field]) -> Field {
    let mut layer = coefficients.to_vec();
    for challenge in point {
        layer = fold_coefficients(&layer, *challenge);
    }
    layer.first().copied().unwrap_or_else(Field::zero)
}

// small folds (the late rounds) are faster without rayon
const PARALLEL_FOLD_MIN: usize = 1 << 12;

/// The line the prover sends each round: (f(0, tail), f(1, tail))
pub fn line_endpoints(coefficients: &[Field], tail: &[Field]) -> (Field, Field) {
    if coefficients.len() == 1 {
        return (coefficients[0], coefficients[0]);
    }
    debug_assert_eq!(coefficients.len(), 2usize << tail.len());

    let mut layer: Option<Vec<Field>> = None;
    for challenge in tail {
        let source = layer.as_deref().unwrap_or(coefficients);
        layer = Some(fold_interleaved_pairs(source, *challenge));
    }
    let last = layer.as_deref().unwrap_or(coefficients);
    let at_zero = last[0];
    (at_zero, at_zero + last[1])
}

fn fold_interleaved_pairs(source: &[Field], challenge: Field) -> Vec<Field> {
    let fold = |quad: &[Field], out: &mut [Field]| {
        out[0] = quad[0] + challenge * quad[2];
        out[1] = quad[1] + challenge * quad[3];
    };
    let mut out = vec![Field::zero(); source.len() / 2];
    if out.len() >= PARALLEL_FOLD_MIN {
        out.par_chunks_mut(2)
            .zip(source.par_chunks_exact(4))
            .with_min_len(PARALLEL_FOLD_MIN / 2)
            .for_each(|(out, quad)| fold(quad, out));
    } else {
        out.chunks_mut(2)
            .zip(source.chunks_exact(4))
            .for_each(|(out, quad)| fold(quad, out));
    }
    out
}

pub fn line_evaluate(line: (Field, Field), point: Field) -> Field {
    line.0 * (Field::one() - point) + line.1 * point
}

pub fn deep_point_powered(mut value: Field, length: usize) -> Vec<Field> {
    let mut point = Vec::with_capacity(length);
    for _ in 0..length {
        point.push(value);
        value.square_in_place();
    }
    point
}

#[cfg(test)]
mod tests {
    use super::*;

    // Slow version that splits even/odd coefficients, to check line_endpoints
    fn line_endpoints_reference(coefficients: &[Field], tail: &[Field]) -> (Field, Field) {
        if coefficients.len() == 1 {
            return (coefficients[0], coefficients[0]);
        }
        let even = coefficients.iter().step_by(2).copied().collect::<Vec<_>>();
        let odd = coefficients
            .iter()
            .skip(1)
            .step_by(2)
            .copied()
            .collect::<Vec<_>>();
        let at_zero = evaluate_multilinear(&even, tail);
        (at_zero, at_zero + evaluate_multilinear(&odd, tail))
    }

    #[test]
    fn boolean_point_shortcut() {
        let num_vars = 7;
        let evaluations = (0..1u64 << num_vars)
            .map(|i| Field::from(i.wrapping_mul(0x2545_f491_4f6c_dd1d) ^ 0x77))
            .collect::<Vec<_>>();
        let polynomial =
            MultilinearPolynomial::from_boolean_evaluations(evaluations.clone()).unwrap();
        for slot in 0..1usize << num_vars {
            let point = (0..num_vars)
                .map(|variable| Field::from(((slot >> variable) & 1) as u64))
                .collect::<Vec<_>>();
            assert_eq!(boolean_slot(&point), Some(slot));
            assert_eq!(polynomial.evaluate(&point).unwrap(), evaluations[slot]);
            assert_eq!(
                evaluate_multilinear(polynomial.coefficients(), &point),
                evaluations[slot]
            );
        }
        let mut mixed = vec![Field::one(); num_vars];
        mixed[3] = Field::from(2u64);
        assert_eq!(boolean_slot(&mixed), None);
        assert_eq!(
            polynomial.evaluate(&mixed).unwrap(),
            evaluate_multilinear(polynomial.coefficients(), &mixed)
        );
    }

    #[test]
    fn line_endpoints_matches_naive() {
        for num_vars in [0usize, 1, 2, 5, 13, 15] {
            let coefficients = (0..1u64 << num_vars)
                .map(|i| Field::from(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x5555))
                .collect::<Vec<_>>();
            let tail = (0..num_vars.saturating_sub(1))
                .map(|i| Field::from(3 + 7 * i as u64))
                .collect::<Vec<_>>();
            assert_eq!(
                line_endpoints(&coefficients, &tail),
                line_endpoints_reference(&coefficients, &tail),
                "num_vars = {num_vars}"
            );
        }
    }
}
