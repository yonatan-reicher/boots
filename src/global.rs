macro_rules! with_variable {
    ($variables:expr,
     $( ($name:expr, $value:expr) ),+,
     $do:expr) => {{
        // Insert the variables.
        $(
            let old = $variables.insert($name.clone(), $value);
        )+

        let x = $do;

        // Remove the variables and put old values back in their place.
        $(
            if let Some(old) = old {
                $variables.insert($name.clone(), old);
            } else {
                $variables.remove($name);
            }
        )+
        x
    }};
}
pub(crate) use with_variable;

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

pub fn collect_results<T, E>(results: impl IntoIterator<Item = Result<T, E>>) -> Result<Vec<T>, Vec<E>> {
    let mut ret: Result<Vec<_>, Vec<_>> = Ok(vec![]);

    for result in results {
        match result {
            Ok(x) => ret = ret.map(|mut v| {
                v.push(x);
                v
            }),
            Err(e) => ret = ret.map_err(|mut v| {
                v.push(e);
                v
            }),
        }
    }

    ret
}

#[inline]
pub fn destruct<T, U, E: Copy>(result: Result<(T, U), E>) -> (Result<T, E>, Result<U, E>) {
    match result {
        Ok((t, u)) => (Ok(t), Ok(u)),
        Err(e) => (Err(e), Err(e)),
    }
}

