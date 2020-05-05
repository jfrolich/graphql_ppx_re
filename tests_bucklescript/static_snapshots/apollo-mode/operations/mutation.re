[@ocaml.ppx.context
  {
    tool_name: "migrate_driver",
    include_dirs: [],
    load_path: [],
    open_modules: [],
    for_package: None,
    debug: false,
    use_threads: false,
    use_vmthreads: false,
    recursive_types: false,
    principal: false,
    transparent_modules: false,
    unboxed_types: false,
    unsafe_string: false,
    cookies: [],
  }
];
module MyQuery = {
  module Raw = {
    type t_mutationWithError_value = {
      __typename: string,
      stringField: string,
    };
    type t_mutationWithError_errors_field = string;
    type t_mutationWithError_errors = {
      __typename: string,
      field: t_mutationWithError_errors_field,
      message: string,
    };
    type t_mutationWithError = {
      __typename: string,
      value: Js.Nullable.t(t_mutationWithError_value),
      errors: Js.Nullable.t(array(t_mutationWithError_errors)),
    };
    type t = {mutationWithError: t_mutationWithError};
  };
  let query = "mutation   {\nmutationWithError  {\n__typename  \nvalue  {\n__typename  \nstringField  \n}\n\nerrors  {\n__typename  \nfield  \nmessage  \n}\n\n}\n\n}\n";
  type t_mutationWithError_value = {
    __typename: string,
    stringField: string,
  };
  type t_mutationWithError_errors_field = [
    | `FutureAddedValue(string)
    | `FIRST
    | `SECOND
    | `THIRD
  ];
  type t_mutationWithError_errors = {
    __typename: string,
    field: t_mutationWithError_errors_field,
    message: string,
  };
  type t_mutationWithError = {
    __typename: string,
    value: option(t_mutationWithError_value),
    errors: option(array(t_mutationWithError_errors)),
  };
  type t = {mutationWithError: t_mutationWithError};
  type operation = t;
  let parse: Raw.t => t =
    (value) => (
      {
        let mutationWithError = {
          let value = (value: Raw.t).mutationWithError;
          (
            {
              let errors = {
                let value = (value: Raw.t_mutationWithError).errors;
                switch (Js.toOption(value)) {
                | Some(value) =>
                  Some(
                    value
                    |> Js.Array.map((value) =>
                         (
                           {
                             let message = {
                               let value =
                                 (value: Raw.t_mutationWithError_errors).
                                   message;
                               value;
                             }
                             and field = {
                               let value =
                                 (value: Raw.t_mutationWithError_errors).field;
                               switch (Obj.magic(value: string)) {
                               | "FIRST" => `FIRST
                               | "SECOND" => `SECOND
                               | "THIRD" => `THIRD
                               | other => `FutureAddedValue(other)
                               };
                             }
                             and __typename = {
                               let value =
                                 (value: Raw.t_mutationWithError_errors).
                                   __typename;
                               value;
                             };
                             {__typename, field, message};
                           }: t_mutationWithError_errors
                         )
                       ),
                  )
                | None => None
                };
              }
              and value = {
                let value = (value: Raw.t_mutationWithError).value;
                switch (Js.toOption(value)) {
                | Some(value) =>
                  Some(
                    {
                      let stringField = {
                        let value =
                          (value: Raw.t_mutationWithError_value).stringField;
                        value;
                      }
                      and __typename = {
                        let value =
                          (value: Raw.t_mutationWithError_value).__typename;
                        value;
                      };
                      {__typename, stringField};
                    }: t_mutationWithError_value,
                  )
                | None => None
                };
              }
              and __typename = {
                let value = (value: Raw.t_mutationWithError).__typename;
                value;
              };
              {__typename, value, errors};
            }: t_mutationWithError
          );
        };
        {mutationWithError: mutationWithError};
      }: t
    );
  let serialize: t => Raw.t =
    (value) => (
      {
        let mutationWithError = {
          let value = (value: t).mutationWithError;
          (
            {
              let errors = {
                let value = (value: t_mutationWithError).errors;
                switch (value) {
                | Some(value) =>
                  Js.Nullable.return(
                    value
                    |> Js.Array.map((value) =>
                         (
                           {
                             let message = {
                               let value =
                                 (value: t_mutationWithError_errors).message;
                               value;
                             }
                             and field = {
                               let value =
                                 (value: t_mutationWithError_errors).field;
                               switch (value) {
                               | `FIRST => "FIRST"
                               | `SECOND => "SECOND"
                               | `THIRD => "THIRD"
                               | `FutureAddedValue(other) => other
                               };
                             }
                             and __typename = {
                               let value =
                                 (value: t_mutationWithError_errors).
                                   __typename;
                               value;
                             };
                             {__typename, field, message};
                           }: Raw.t_mutationWithError_errors
                         )
                       ),
                  )
                | None => Js.Nullable.null
                };
              }
              and value = {
                let value = (value: t_mutationWithError).value;
                switch (value) {
                | Some(value) =>
                  Js.Nullable.return(
                    {
                      let stringField = {
                        let value =
                          (value: t_mutationWithError_value).stringField;
                        value;
                      }
                      and __typename = {
                        let value =
                          (value: t_mutationWithError_value).__typename;
                        value;
                      };
                      {__typename, stringField};
                    }: Raw.t_mutationWithError_value,
                  )
                | None => Js.Nullable.null
                };
              }
              and __typename = {
                let value = (value: t_mutationWithError).__typename;
                value;
              };
              {__typename, value, errors};
            }: Raw.t_mutationWithError
          );
        };
        {mutationWithError: mutationWithError};
      }: Raw.t
    );
  let definition = (parse, query, serialize);
};