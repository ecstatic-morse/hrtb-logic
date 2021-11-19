//! Recursive iteration over `Formula`s using the visitor pattern.

#[allow(unused_imports)]
use std::ops::ControlFlow::{self as Flow, Break, Continue};

use paste::paste;

use crate::{Formula, Var};

macro_rules! make_visitor {
    ([$($mt:tt)?]) => {
        paste! {
            make_visitor!(
                [<Visit $($mt:camel)?>]
                [<AnonFormVisitor $($mt:camel)?>]
                [<Cont $($mt:camel)?>]
                [<cont $(_ $mt)?>]
                [$($mt)?]
            );
        }
    };

    ($Visit:ident $Anon:ident $Cont:ident $cont:ident [$($mt:tt)?]) => {
        pub trait $Visit {
            type Break;

            fn visit_formula(&mut self, form: & $($mt)? Formula) -> Flow<Self::Break> {
                self.super_formula(form)
            }

            fn visit_var(&mut self, _var: & $($mt)? Var) -> Flow<Self::Break> {
                Continue(())
            }

            fn super_formula(&mut self, form: & $($mt)? Formula) -> Flow<Self::Break> {
                match form {
                    | Formula::Trivial(_)
                    | Formula::Prop(_)
                    => Continue(()),

                    Formula::SubsetEq { sub, sup } => {
                        self.visit_var(sub)?;
                        self.visit_var(sup)
                    }

                    Formula::Not(form) => self.visit_formula(form),

                    Formula::Bind(_, var, form) => {
                        self.visit_var(var)?;
                        self.visit_formula(form)
                    }
                    Formula::And(list) | Formula::Or(list) => {
                        for form in list {
                            self.visit_formula(form)?;
                        }

                        Continue(())
                    }
                }
            }
        }

        type $Cont<R, S> = fn(& $($mt)? Formula, &mut S) -> Flow<R>;
        fn $cont<R, S>(_: & $($mt)? Formula, _: &mut S) -> Flow<R> { Continue(()) }

        /// An anonymous `Formula` visitor.
        pub struct $Anon<A, B, S = ()> {
            pub pre: A,
            pub post: B,
            pub state: S,
        }

        impl<F, R> $Anon<F, $Cont<R, ()>>
            where F: FnMut(& $($mt)? Formula, &mut ()) -> Flow<R>
        {
            pub fn pre(pre: F) -> Self {
                Self { pre, post: $cont, state: () }
            }
        }

        impl<F, R> $Anon<$Cont<R, ()>, F>
            where F: FnMut(& $($mt)? Formula, &mut ()) -> Flow<R>
        {
            pub fn post(post: F) -> Self {
                Self { pre: $cont, post, state: () }
            }
        }

        impl<R, A, B, S> $Visit for $Anon<A, B, S>
            where A: FnMut(& $($mt)? Formula, &mut S) -> Flow<R>,
                  B: FnMut(& $($mt)? Formula, &mut S) -> Flow<R>,
        {
            type Break = R;

            fn visit_formula(&mut self, form: & $($mt)? Formula) -> Flow<Self::Break> {
                (self.pre)(form, &mut self.state)?;
                self.super_formula(form)?;
                (self.post)(form, &mut self.state)
            }
        }
    };
}

make_visitor!([]);
make_visitor!([mut]);
