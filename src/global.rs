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
