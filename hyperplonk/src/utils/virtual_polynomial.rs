use ark_ff::fields::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial};
use ark_std::{Zero, One};
use std::ops::{Add, Mul};

#[derive(Clone, Debug)]
pub enum VirtualPolyExpr<F: PrimeField> {
    /// Polynomial input at index
    Input(usize),
    /// Constant polynomial
    Const(F),
    /// Addition of two virtual polynomial expressions
    Add(Box<VirtualPolyExpr<F>>, Box<VirtualPolyExpr<F>>),
    /// Multiplication of two virtual polynomial expressions
    Mul(Box<VirtualPolyExpr<F>>, Box<VirtualPolyExpr<F>>),
}

impl<F: PrimeField> core::fmt::Display for VirtualPolyExpr<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VirtualPolyExpr::Input(i) => write!(f, "g{}", i),
            VirtualPolyExpr::Const(c) => write!(f, "{}", c),
            VirtualPolyExpr::Add(left, right) => write!(f, "({} + {})", left, right),
            VirtualPolyExpr::Mul(left, right) => write!(f, "({} * {})", left, right),
        }
    }
}

impl<F: PrimeField> Add for VirtualPolyExpr<F> {
    type Output = VirtualPolyExpr<F>;

    fn add(self, rhs: Self) -> Self::Output {
        VirtualPolyExpr::Add(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Mul for VirtualPolyExpr<F> {
    type Output = VirtualPolyExpr<F>;

    fn mul(self, rhs: Self) -> Self::Output {
        VirtualPolyExpr::Mul(Box::new(self), Box::new(rhs))
    }
}

impl<F: PrimeField> Zero for VirtualPolyExpr<F> {
    fn zero() -> Self {
        VirtualPolyExpr::Const(F::zero())
    }

    fn is_zero(&self) -> bool {
        match self {
            VirtualPolyExpr::Const(c) => *c == F::zero(),
            _ => false,
        }
    }
}

impl<F: PrimeField> One for VirtualPolyExpr<F> {
    fn one() -> Self {
        VirtualPolyExpr::Const(F::one())
    }

    fn is_one(&self) -> bool {
        match self {
            VirtualPolyExpr::Const(c) => *c == F::one(),
            _ => false,
        }
    }
}


/// A "virtual" polynomial:
/// given multilinear poynomials g1(x), g2(x), ..., gk(x) in n variables,
/// the virtual polynomial v(x) is defined as v(x) = h(g1(x), g2(x), ..., gk(x))
/// for some function h: F^k -> F
/// 
/// The function h has the following structure: it is an arithmetic circuit
/// composed of addition and multiplication gates, with the input wires being
/// the polynomials g1, g2, ..., gk (possibly repeated).
/// 
/// Note: the depth of the circuit directly affects the computational complexity of
/// certain operations on the virtual polynomial, such as evaluation at a point or evaluation
/// over the hypercube {0,1}^n. For example, when multiplying n polynomials together, the
/// expression should be constructed as a balanced binary tree of multiplications to ensure
/// logarithmic depth, rather than a linear chain of multiplications.
pub struct VirtualPolynomial<F: PrimeField> {
    /// Number of variables of the input polynomials
    pub num_vars: usize,
    /// input polynomials g1, g2, ..., gk represented as evaluations over {0,1}^n
    pub polynomials: Vec<Vec<F>>,
    /// expression tree representing the function h
    pub expr: VirtualPolyExpr<F>
}

pub struct VirtualPolynomialInputRef {
    pub index: usize,
}

impl<F: PrimeField> VirtualPolynomial<F> {
    /// Create a new empty virtual polynomial that is the zero polynomial
    pub fn zero(num_vars: usize) -> Self {
        VirtualPolynomial {
            num_vars,
            polynomials: Vec::new(),
            expr: VirtualPolyExpr::Const(F::zero()),
        }
    }

    pub fn new(num_vars: usize, polynomials: Vec<Vec<F>>, expr: VirtualPolyExpr<F>) -> Self {
        assert!(polynomials.iter().all(|p| p.len() == (1 << num_vars)), "Input polynomial evaluations length does not match number of variables");
        VirtualPolynomial {
            num_vars,
            polynomials,
            expr,
        }
    }

    pub fn from_poly_evals(num_vars: usize, poly_evals: Vec<F>) -> (Self, VirtualPolynomialInputRef) {
        assert_eq!(poly_evals.len(), 1 << num_vars, "Input polynomial evaluations length does not match number of variables");
        let vp = VirtualPolynomial {
            num_vars,
            polynomials: vec![poly_evals],
            expr: VirtualPolyExpr::Input(0),
        };
        let vref = VirtualPolynomialInputRef { index: 0 };
        (vp, vref)
    }

    pub fn set_expr(&mut self, expr: VirtualPolyExpr<F>) {
        self.expr = expr;
    }

    /// Allocate a new input polynomial represented by its evaluations over {0,1}^n
    /// and return a reference to it
    pub fn allocate_input_mle(&mut self, poly_evals: Vec<F>) -> VirtualPolynomialInputRef {
        assert_eq!(poly_evals.len(), 1 << self.num_vars, "Input polynomial evaluations length does not match number of variables");
        let index = self.polynomials.len();
        self.polynomials.push(poly_evals);
        VirtualPolynomialInputRef { index }
    }

    /// Add the input polynomial referenced by g_index to the virtual polynomial
    pub fn add_mle(&mut self, g_index: VirtualPolynomialInputRef) {
        self.expr = VirtualPolyExpr::Add(
            Box::new(self.expr.clone()),
            Box::new(VirtualPolyExpr::Input(g_index.index))
        );
    }

    /// Multiply the virtual polynomial by the input polynomial referenced by g_index
    pub fn mul_mle(&mut self, g_index: VirtualPolynomialInputRef) {
        self.expr = VirtualPolyExpr::Mul(
            Box::new(self.expr.clone()),
            Box::new(VirtualPolyExpr::Input(g_index.index))
        );
    }

    /// Evaluate the virtual polynomial given in input univariate polynomials
    /// representing the g_i(x) polynomials
    /// Curretnly this is implemented naively by recursively evaluating the expression tree
    /// and performing polynomial addition and naive multiplication, which is quadratic in the
    /// degree of the polynomials. Therefore, this currently takes O(d^2 * depth) where
    /// d is the degree of h.
    pub fn evaluate_poly(&self, g_polys: &Vec<DensePolynomial<F>>) -> DensePolynomial<F> {
        assert_eq!(g_polys.len(), self.polynomials.len(), "Incorrect number of input polynomials provided for evaluation");
        self.evaluate_expr_poly(&self.expr, &g_polys)
    }

    fn evaluate_expr_poly(&self, expr: &VirtualPolyExpr<F>, g_polys: &Vec<DensePolynomial<F>>) -> DensePolynomial<F> {
        match expr {
            VirtualPolyExpr::Input(i) => {
                g_polys[*i].clone()
            },
            VirtualPolyExpr::Const(c) => {
                DensePolynomial::from_coefficients_slice(&[*c])
            },
            VirtualPolyExpr::Add(left, right) => {
                let left_poly = self.evaluate_expr_poly(left, g_polys);
                let right_poly = self.evaluate_expr_poly(right, g_polys);
                &left_poly + &right_poly
            },
            VirtualPolyExpr::Mul(left, right) => {
                let left_poly = self.evaluate_expr_poly(left, g_polys);
                let right_poly = self.evaluate_expr_poly(right, g_polys);
                // TODO: do fast multiplication
                &left_poly * &right_poly
            },
        }
    }

    /// Evaluate the virtual polynomial over the 
    pub fn evaluate_point(&self, g_evals: &Vec<F>) -> F {
        assert_eq!(g_evals.len(), self.polynomials.len(), "Incorrect number of input polynomial evaluations provided for evaluation");
        self.evaluate_expr(&self.expr, g_evals)
    }

    fn evaluate_expr(&self, expr: &VirtualPolyExpr<F>, g_evals: &Vec<F>) -> F {
        match expr {
            VirtualPolyExpr::Input(i) => {
                g_evals[*i]
            },
            VirtualPolyExpr::Const(c) => {
                *c
            },
            VirtualPolyExpr::Add(left, right) => {
                let left_val = self.evaluate_expr(left, &g_evals);
                let right_val = self.evaluate_expr(right, &g_evals);
                left_val + right_val
            },
            VirtualPolyExpr::Mul(left, right) => {
                let left_val = self.evaluate_expr(left, &g_evals);
                let right_val = self.evaluate_expr(right, &g_evals);
                left_val * right_val
            },
        }
    }
}