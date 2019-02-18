#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Lit(bool),
    Var(String),
    Not(Box<Term>),
    And(Box<Term>, Box<Term>),
    Or(Box<Term>, Box<Term>),
}

use Term::*;

pub fn lit(b: bool) -> Term {
    Lit(b)
}
pub fn var(x: &str) -> Term {
    Var(x.to_string())
}
pub fn not(t: Term) -> Term {
    Not(Box::new(t))
}
pub fn and(t1: Term, t2: Term) -> Term {
    And(Box::new(t1), Box::new(t2))
}
pub fn or(t1: Term, t2: Term) -> Term {
    Or(Box::new(t1), Box::new(t2))
}

impl Term {
    pub fn cnf(&self) -> cnf::Formula {
        // TODO
        unimplemented!()
    }
}

pub mod cnf {
    use itertools::Itertools;
    use std::collections::HashSet;

    type Var = u32;

    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub enum Lit {
        Pos(Var),
        Neg(Var),
    }
    use Lit::{Neg, Pos};

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Clause {
        lits: Vec<Lit>,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Formula {
        /// INVARIANT: all `Clause`s must be `simplify`d
        clauses: Vec<Clause>,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Answer {
        Sat,
        Unsat,
    }
    use Answer::{Sat, Unsat};

    impl Lit {
        pub fn var(&self) -> &Var {
            match self {
                Pos(v) => v,
                Neg(v) => v,
            }
        }
        pub fn is_pos_of(&self, v: &Var) -> bool {
            match self {
                Pos(x) => v == x,
                Neg(_) => false,
            }
        }
        pub fn is_neg_of(&self, v: &Var) -> bool {
            match self {
                Pos(_) => false,
                Neg(x) => v == x,
            }
        }
        pub fn negate(&self) -> Self {
            match self {
                Pos(v) => Neg(*v),
                Neg(v) => Pos(*v),
            }
        }
    }
    impl From<i32> for Lit {
        fn from(v: i32) -> Lit {
            if v > 0 {
                Pos(v as Var)
            } else if v < 0 {
                Neg(-v as Var)
            } else {
                panic!("Lit must be non-zero")
            }
        }
    }

    impl Clause {
        pub fn new(lits: &[Lit]) -> Self {
            Clause {
                lits: lits.to_vec(),
            }
        }
        pub fn empty(&self) -> bool {
            self.lits.is_empty()
        }
        /// Simplifies a `Clause`, returns `None` if it's a tautology
        pub fn simplify(&self) -> Option<Self> {
            let mut seen = HashSet::new();
            for lit in self.lits.iter() {
                if seen.contains(&lit.negate()) {
                    return None;
                } else {
                    seen.insert(lit.clone());
                }
            }
            Some(Clause { lits: seen.into_iter().collect() })
        }
    }
    impl From<Vec<i32>> for Clause {
        fn from(lits: Vec<i32>) -> Clause {
            Clause { lits: lits.into_iter().map(Lit::from).collect() }
        }
    }

    impl Formula {
        pub fn new(clauses: &[Clause]) -> Self {
            Formula {
                clauses: clauses.to_vec(),
            }
        }
        pub fn empty(&self) -> bool {
            self.clauses.is_empty()
        }
        pub fn vars(&self) -> impl Iterator<Item = &Var> {
            self.clauses
                .iter()
                .flat_map(|cl| cl.lits.iter().map(|l| l.var()))
                .unique()
        }
        pub fn is_pure(&self, v: &Var) -> bool {
            let ps: usize = self
                .clauses
                .iter()
                .map(|cl| cl.lits.iter().filter(|l| l.is_pos_of(v)).count())
                .sum();
            let ns: usize = self
                .clauses
                .iter()
                .map(|cl| cl.lits.iter().filter(|l| l.is_neg_of(v)).count())
                .sum();
            ps == 0 || ns == 0
        }
        pub fn is_trivial(&self) -> Result<Answer, Var> {
            if self.clauses.is_empty() {
                Ok(Sat)
            } else if self.clauses.iter().any(|cl| cl.lits.is_empty()) {
                Ok(Unsat)
            } else if let Some(pivot) = self.vars().find(|v| !self.is_pure(v)) {
                Err(pivot.clone())
            } else {
                Ok(Sat)
            }
        }
        pub fn resolve(&self, pivot: &Var) -> Self {
            let (with, mut without): (Vec<Clause>, Vec<Clause>) = self
                .clauses
                .iter()
                .cloned()
                .partition(|cl| cl.lits.iter().any(|l| l.var() == pivot));
            let new: Vec<Lit> = with
                .iter()
                .flat_map(|cl| cl.lits.iter().cloned().filter(|l| l.var() != pivot))
                .collect();
            // println!("with: {:?}\nwithout: {:?}\nnew: {:?}\n", with, without, new);
            if let Some(cl) = (Clause{ lits: new}).simplify() {
                without.push(cl);
            }
            Formula { clauses: without }
        }
        pub fn dp(&self) -> Answer {
            match self.is_trivial() {
                Ok(ans) => ans,
                Err(pivot) => self.resolve(&pivot).dp(),
            }
        }
    }
    impl From<Vec<Vec<i32>>> for Formula {
        fn from(clauses: Vec<Vec<i32>>) -> Formula {
            Formula {
                clauses: clauses
                    .into_iter()
                    .map(Clause::from)
                    .filter_map(|cl| cl.simplify())
                    .collect()
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::cnf::*;

        #[test]
        fn is_pure_works() {
            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                    Clause {
                        lits: vec![Pos(1), Pos(2)],
                    },
                ],
            };
            assert!(phi.is_pure(&1));

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Neg(1)] },
                    Clause {
                        lits: vec![Neg(1), Pos(2)],
                    },
                ],
            };
            assert!(phi.is_pure(&1));

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Neg(1)] },
                    Clause {
                        lits: vec![Pos(1), Pos(2)],
                    },
                ],
            };
            assert!(!phi.is_pure(&1));
        }
        #[test]
        fn is_trivial_works() {
            let phi = Formula { clauses: vec![] };
            assert_eq!(phi.is_trivial(), Ok(Sat));

            let phi = Formula {
                clauses: vec![Clause { lits: vec![Pos(1)] }],
            };
            assert_eq!(phi.is_trivial(), Ok(Sat));

            let phi = Formula {
                clauses: vec![Clause { lits: vec![Pos(1)] }, Clause { lits: vec![] }],
            };
            assert_eq!(phi.is_trivial(), Ok(Unsat));

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                    Clause { lits: vec![Pos(1)] },
                ],
            };
            assert_eq!(phi.is_trivial(), Ok(Sat));

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1), Neg(1)] },
                ],
            };
            assert_eq!(phi.is_trivial(), Err(1));

            let phi = Formula {
                clauses: vec![
                    Clause {
                        lits: vec![Pos(1), Neg(2)],
                    },
                    Clause {
                        lits: vec![Pos(1), Neg(2)],
                    },
                ],
            };
            assert_eq!(phi.is_trivial(), Ok(Sat));

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                    Clause { lits: vec![Neg(1)] },
                ],
            };
            assert_eq!(phi.is_trivial(), Err(1));

            let phi = Formula::from(
                vec![
                    vec![2 , -3],
                    vec![-2 ,  3],
                ]
            );
            assert_eq!(phi.is_trivial(), Err(3));
        }
        #[test]
        fn resolve_works() {
            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                    Clause { lits: vec![Neg(1)] },
                ],
            };
            assert_eq!(phi.resolve(&1), Formula::new(&[Clause::new(&[])]));
            assert_eq!(phi.resolve(&1).is_trivial(), Ok(Unsat));

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Neg(1), Pos(2)] },
                    Clause { lits: vec![Pos(1)] },
                ],
            };
            assert_eq!(phi.resolve(&1), Formula::from(vec![vec![2]]));
            assert_eq!(phi.resolve(&1).is_trivial(), Ok(Sat));

            // let phi = Formula {
            //     clauses: vec![
            //         Clause { lits: vec![Pos(1), Neg(1)] },
            //     ],
            // };
            // assert_eq!(phi.resolve(&1), Formula::from(vec![]));
            // assert_eq!(phi.resolve(&1).is_trivial(), Ok(Sat));

            let phi = Formula::from(
                vec![
                    vec![2 , -3],
                    vec![-2 ,  3],
                ]
            );
            assert_eq!(phi.resolve(&2), Formula::from(vec![]));
            assert_eq!(phi.resolve(&2).is_trivial(), Ok(Sat));
        }
        #[test]
        fn dp_works() {
            let phi = Formula {
                clauses: vec![],
            };
            assert_eq!(phi.dp(), Sat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![] },
                ],
            };
            assert_eq!(phi.dp(), Unsat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                ],
            };
            assert_eq!(phi.dp(), Sat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Neg(1)] },
                ],
            };
            assert_eq!(phi.dp(), Sat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1), Neg(1)] },
                ],
            };
            assert_eq!(phi.dp(), Unsat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1), Neg(2)] },
                ],
            };
            assert_eq!(phi.dp(), Sat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                    Clause { lits: vec![Neg(1)] },
                ],
            };
            assert_eq!(phi.dp(), Unsat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1)] },
                    Clause { lits: vec![Neg(2)] },
                ],
            };
            assert_eq!(phi.dp(), Sat);

            // can't construct this one directly as it's not simplified..
            // let phi = Formula {
            //     clauses: vec![
            //         Clause { lits: vec![Pos(1), Neg(1)] },
            //     ],
            // };
            let phi = Formula::from(vec![ vec![1, -1] ]);
            assert_eq!(phi.dp(), Sat);

            let phi = Formula {
                clauses: vec![
                    Clause { lits: vec![Pos(1), Pos(2)] },
                    Clause { lits: vec![Neg(1), Pos(3)] },
                    Clause { lits: vec![Neg(3)] },
                ],
            };
            assert_eq!(phi.dp(), Sat);

            let phi = Formula::from(
                vec![
                    vec![2 , -3],
                    vec![-2 ,  3],
                ]
            );
            assert_eq!(phi.dp(), Sat);

            let phi = Formula::from(
                vec![
                    vec![-9 ,  1 ,  2],
                    vec![ 9 ,  2 ,  3],
                    vec![ 9 ,  2 , -3],
                    vec![ 9 , -2 ,  3],
                    vec![ 9 , -2 , -3],
                    vec![-1 , -2 ,  3],
                    vec![-9 ,  1 , -2],
                    vec![-9 , -1 ,  2],
                ]
            );
            assert_eq!(phi.dp(), Sat);

            let phi = Formula::from(
                vec![
                    vec![ 1 ,  4],
                    vec![ 1 , -3,  -8],
                    vec![ 1 ,  8,  12],
                    vec![ 2 , 11],
                    vec![-7 , -3,   9],
                    vec![-7 ,  8,  -9],
                    vec![ 7 ,  8, -10],
                    vec![ 7 , 10, -12],
                ]
            );
            assert_eq!(phi.dp(), Sat);
        }
    }
}
