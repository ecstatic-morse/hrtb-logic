macro_rules! unwrap {
    (let $pat:pat = $expr:expr) => {
        let $pat = $expr else {
                            panic!("{} did not match {}", stringify!($expr), stringify!($pat));
                        };
    };
}
