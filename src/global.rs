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

pub fn extend<T, I: IntoIterator<Item = T>>(mut left: Vec<T>, right: I) -> Vec<T> {
    left.extend(right);
    left
}

pub trait VecPipe<T>: Into<Vec<T>> {
    fn extend_pipe<I: IntoIterator<Item = T>>(self, right: I) -> Vec<T> {
        extend(self.into(), right)
    }

    fn extend_pipe_one(self, right: T) -> Vec<T> {
        let mut v = self.into();
        v.push(right);
        v
    }
}

impl<T, V> VecPipe<T> for V where V: Into<Vec<T>> {}

pub trait Pipe<T, U>: Into<T> {
    fn pipe(self, f: impl FnOnce(T) -> U) -> U {
        f(self.into())
    }
}

impl<T, U> Pipe<T, U> for T {}
