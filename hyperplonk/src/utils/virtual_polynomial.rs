use ark_ff::fields::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly::DenseMultilinearExtension;
use ark_poly::{DenseUVPolynomial};
use ark_std::{Zero, One};
use std::ops::{Add, Mul, Sub};

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

impl<F: PrimeField> Sub for VirtualPolyExpr<F> {
    type Output = VirtualPolyExpr<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        let neg_rhs = VirtualPolyExpr::Mul(Box::new(VirtualPolyExpr::Const(F::one().neg())), Box::new(rhs));
        VirtualPolyExpr::Add(Box::new(self), Box::new(neg_rhs))
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

#[derive(Clone, Debug)]
pub struct VirtualPolynomialInputRef {
    pub index: usize,
}

impl VirtualPolynomialInputRef {
    pub fn to_expr<F : PrimeField>(&self) -> VirtualPolyExpr<F> {
        VirtualPolyExpr::Input(self.index)
    }
}

#[derive(Clone, Debug)]
pub struct VirtualPolynomialRef {
    pub index: usize,
}


/// A "virtual" polynomial:
/// given a set of multilinear poynomials g1(x), g2(x), ..., gk(x) in n variables,
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
#[derive(Clone, Debug)]
pub struct VirtualPolynomialStore<F: PrimeField> {
    /// Number of variables for the polynomials in the store
    pub num_vars: usize,
    /// Polynomials stored as evaluations over {0,1}^num_vars
    pub polynomials: Vec<DenseMultilinearExtension<F>>,
    /// expression tree representing the function h
    pub virtual_polys: Vec<VirtualPolyExpr<F>>
}

impl<F: PrimeField> VirtualPolynomialStore<F> {
    pub fn new(num_vars: usize) -> Self {
        VirtualPolynomialStore {
            num_vars,
            polynomials: Vec::new(),
            virtual_polys: Vec::new(),
        }
    }

    /// Add a polynomial represented by its evaluations over {0,1}^n to the store
    pub fn allocate_polynomial(&mut self, poly_evals: &Vec<F>) -> VirtualPolynomialInputRef {
        assert_eq!(poly_evals.len(), 1 << self.num_vars, "Input polynomial evaluations length does not match number of variables");
        let index = self.polynomials.len();
        let mle = DenseMultilinearExtension::from_evaluations_slice(self.num_vars, poly_evals);
        self.polynomials.push(mle);
        VirtualPolynomialInputRef { index }
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Create a new virtual polynomial in the store that is initially equal to the
    /// input polynomial referenced by g
    /// Assumes g references a polynomial already in the store
    pub fn new_virtual_from_input(&mut self, g: &VirtualPolynomialInputRef) -> VirtualPolynomialRef {
        let expr = VirtualPolyExpr::Input(g.index);
        let index = self.virtual_polys.len();
        self.virtual_polys.push(expr);
        VirtualPolynomialRef {
            index,
        }
    }

    pub fn new_virtual_from_virtual(&mut self, v: &VirtualPolynomialRef) -> VirtualPolynomialRef {
        let expr = self.virtual_polys[v.index].clone();
        let index = self.virtual_polys.len();
        self.virtual_polys.push(expr);
        VirtualPolynomialRef {
            index,
        }
    }

    pub fn new_virtual_from_expr(&mut self, expr: VirtualPolyExpr<F>) -> VirtualPolynomialRef {
        let index = self.virtual_polys.len();
        self.virtual_polys.push(expr);
        VirtualPolynomialRef {
            index,
        }
    }

    /// Create a new virtual polynomial in the store that is identically zero
    pub fn new_virtual_zero(&mut self) -> VirtualPolynomialRef {
        let expr = VirtualPolyExpr::zero();
        let index = self.virtual_polys.len();
        self.virtual_polys.push(expr);
        VirtualPolynomialRef {
            index,
        }
    }

    /// Create a new virtual polynomial in the store that is identically one
    pub fn new_virtual_one(&mut self) -> VirtualPolynomialRef {
        let expr = VirtualPolyExpr::one();
        let index = self.virtual_polys.len();
        self.virtual_polys.push(expr);
        VirtualPolynomialRef {
            index,
        }
    }

    /// Replace the virtual polynomial referenced by f_index with the sum of itself and
    /// the input polynomial referenced by g_index
    pub fn add_in_place(&mut self, f_index: &VirtualPolynomialRef, g_index: &VirtualPolynomialInputRef) {
        let f_expr = self.virtual_polys[f_index.index].clone();
        let g_expr = VirtualPolyExpr::Input(g_index.index);
        self.virtual_polys[f_index.index] = VirtualPolyExpr::Add(Box::new(f_expr), Box::new(g_expr));
    }

    /// Replace the virtual polynomial referenced by f_index with the sum of itself and
    /// the constant polynomial c
    pub fn add_const_in_place(&mut self, f_index: &VirtualPolynomialRef, c: F) {
        let f_expr = self.virtual_polys[f_index.index].clone();
        let c_expr = VirtualPolyExpr::Const(c);
        self.virtual_polys[f_index.index] = VirtualPolyExpr::Add(Box::new(f_expr), Box::new(c_expr));
    }

    /// Replace the virtual polynomial referenced by f_index with the difference of itself and
    /// the input polynomial referenced by g_index
    pub fn sub_in_place(&mut self, f_index: &VirtualPolynomialRef, g_index: &VirtualPolynomialInputRef) {
        let f_expr = self.virtual_polys[f_index.index].clone();
        let g_expr = VirtualPolyExpr::Input(g_index.index);
        let neg_g_expr = VirtualPolyExpr::Mul(Box::new(VirtualPolyExpr::Const(F::from(-1i32))), Box::new(g_expr));
        self.virtual_polys[f_index.index] = VirtualPolyExpr::Add(Box::new(f_expr), Box::new(neg_g_expr));
    }

    /// Replace the virtual polynomial referenced by f_index with the product of itself and
    /// the input polynomial referenced by g_index
    pub fn mul_in_place(&mut self, f_index: &VirtualPolynomialRef, g_index: &VirtualPolynomialInputRef) {
        let f_expr = self.virtual_polys[f_index.index].clone();
        let g_expr = VirtualPolyExpr::Input(g_index.index);
        self.virtual_polys[f_index.index] = VirtualPolyExpr::Mul(Box::new(f_expr), Box::new(g_expr));
    }

    /// Evaluate the virtual polynomial given in input univariate polynomials
    /// representing the g_i(x) polynomials
    /// Curretnly this is implemented naively by recursively evaluating the expression tree
    /// and performing polynomial addition and naive multiplication, which is quadratic in the
    /// degree of the polynomials. Therefore, this currently takes O(d^2 * depth) where
    /// d is the degree of h.
    pub fn evaluate_poly(&self, g_polys: &Vec<DensePolynomial<F>>, virtual_index: &VirtualPolynomialRef) -> DensePolynomial<F> {
        assert_eq!(g_polys.len(), self.polynomials.len(), "Incorrect number of input polynomials provided for evaluation");
        let expr = &self.virtual_polys[virtual_index.index];
        self.evaluate_expr_poly(expr, &g_polys)
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
    pub fn evaluate_point(&self, g_evals: &Vec<F>, virtual_index: &VirtualPolynomialRef) -> F {
        assert_eq!(g_evals.len(), self.polynomials.len(), "Incorrect number of input polynomial evaluations provided for evaluation");
        let expr = &self.virtual_polys[virtual_index.index];
        self.evaluate_expr(expr, g_evals)
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