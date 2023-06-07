use std::collections::HashMap;
use std::hash::Hash;

pub trait Withable<In> {
    type Hid;

    fn begin(self, x: In) -> Self::Hid;
    fn end(self, hid: Self::Hid);
}

impl<K, V> Withable<(K, V)> for &mut HashMap<K, V>
where
    K: Eq + Hash + Clone,
{
    type Hid = (K, Option<V>);

    fn begin(self, (k, v): (K, V)) -> (K, Option<V>) {
        (k.clone(), self.insert(k, v))
    }

    fn end(self, (k, old_val): (K, Option<V>)) {
        match old_val {
            Some(old_val) => self.insert(k, old_val),
            None => self.remove(&k),
        };
    }
}

impl<T> Withable<T> for &mut Vec<T> {
    type Hid = ();

    fn begin(self, x: T) {
        self.push(x);
    }

    fn end(self, _: ()) {
        self.pop();
    }
}

macro_rules! with_variable {
    ($variables:expr, $var:expr, $do:expr) => {{
        let old = $variables.begin($var);
        let x = $do;
        $variables.end(old);
        x
    }};
}

pub(crate) use with_variable;

macro_rules! with_variables {
    ($variables:expr, $variables_to_add:expr, $do:expr) => {{
        let old_values = $variables_to_add
            .into_iter()
            .map(|x| $variables.begin(x))
            .collect::<Vec<_>>();

        let x = $do;

        for old_value in old_values {
            $variables.end(old_value);
        }

        x
    }};
}
pub(crate) use with_variables;

#[inline]
pub fn extend<T, E: Extend<T>, I: IntoIterator<Item = T>>(mut left: E, right: I) -> E {
    left.extend(right);
    left
}

pub trait ExtendPipe<T, E: Extend<T>>: Into<E> {
    #[inline]
    fn extend_pipe<I: IntoIterator<Item = T>>(self, right: I) -> E {
        extend(self.into(), right)
    }

    #[inline]
    fn extend_pipe_one(self, right: T) -> E {
        self.extend_pipe(Some(right))
    }
}

impl<T, E: Extend<T>> ExtendPipe<T, E> for E {}

pub trait Pipe<T, U>: Into<T> {
    #[inline]
    fn pipe(self, f: impl FnOnce(T) -> U) -> U {
        f(self.into())
    }
}

impl<T, U> Pipe<T, U> for T {}

pub fn collect_results<T, E>(
    results: impl IntoIterator<Item = Result<T, E>>,
) -> Result<Vec<T>, Vec<E>> {
    let mut ret: Result<Vec<_>, Vec<_>> = Ok(vec![]);

    for result in results {
        match result {
            Ok(x) => {
                ret = ret.map(|mut v| {
                    v.push(x);
                    v
                })
            }
            Err(e) => {
                ret = ret.map_err(|mut v| {
                    v.push(e);
                    v
                })
            }
        }
    }

    ret
}

// TODO: Rename to unzip
#[inline]
pub fn destruct<T, U, E: Copy>(result: Result<(T, U), E>) -> (Result<T, E>, Result<U, E>) {
    match result {
        Ok((t, u)) => (Ok(t), Ok(u)),
        Err(e) => (Err(e), Err(e)),
    }
}

pub fn is_sorted<T: Ord>(data: &[T]) -> bool {
    data.windows(2).all(|w| w[0] <= w[1])
}
