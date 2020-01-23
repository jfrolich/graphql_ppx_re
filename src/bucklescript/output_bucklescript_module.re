open Graphql_ppx_base;
open Result_structure;
open Generator_utils;

open Ast_406;
open Asttypes;
open Parsetree;
open Ast_helper;
open Extract_type_definitions;

module StringSet = Set.Make(String);
module VariableFinderImpl = {
  type t = ref(StringSet.t);
  let make_self = _ => ref(StringSet.empty);

  include Traversal_utils.AbstractVisitor;

  let enter_variable_value = (self, _, v) =>
    self := StringSet.add(v.Source_pos.item, self^);

  let from_self = (self: t): StringSet.t => self^;
};

module VariableFinder = Traversal_utils.Visitor(VariableFinderImpl);

let find_variables = (config, document) => {
  let ctx = Traversal_utils.make_context(config, document);
  VariableFinderImpl.from_self(VariableFinder.visit_document(ctx, document));
};

let join = (part1, part2) => {
  Ast_helper.(
    Exp.apply(
      Exp.ident({Location.txt: Longident.parse("^"), loc: Location.none}),
      [(Nolabel, part1), (Nolabel, part2)],
    )
  );
};

// port of split_on_char from the stdlib because it was only introduced
// in ocaml 4.04
let split_on_char = (sep, s) => {
  let r = ref([]);
  let j = ref(String.length(s));
  for (i in String.length(s) - 1 downto 0) {
    if (String.unsafe_get(s, i) == sep) {
      r := [String.sub(s, i + 1, j^ - i - 1), ...r^];
      j := i;
    };
  };
  [String.sub(s, 0, j^), ...r^];
};

let pretty_print = (query: string): string => {
  let indent = ref(1);

  let str =
    query
    |> split_on_char('\n')
    |> List.map(l => String.trim(l))
    |> List.filter(l => l != "")
    |> List.map(line => {
         if (String.contains(line, '}')) {
           indent := indent^ - 1;
         };
         let line = String.make(indent^ * 2, ' ') ++ line;
         if (String.contains(line, '{')) {
           indent := indent^ + 1;
         };
         line;
       })
    |> String.concat("\n");

  str ++ "\n";
};

let compress_parts = (parts: array(Graphql_printer.t)) => {
  Graphql_printer.(
    parts
    |> Array.to_list
    |> List.fold_left(
         (acc, curr) => {
           switch (acc, curr) {
           | ([String(s1), ...rest], String(s2)) => [
               String(s1 ++ s2),
               ...rest,
             ]
           | (acc, Empty) => acc
           | (acc, curr) => [curr, ...acc]
           }
         },
         [],
       )
    |> List.rev
    |> Array.of_list
  );
};

let emit_printed_query = (~strProcess=?, parts) => {
  open Ast_406;
  let make_string = s => {
    Exp.constant(Parsetree.Pconst_string(s, None));
  };
  let make_fragment_name = f => {
    Exp.ident({
      Location.txt: Longident.parse(f ++ ".name"),
      loc: Location.none,
    });
  };
  let make_fragment_query = f => {
    Exp.ident({
      Location.txt: Longident.parse(f ++ ".query"),
      loc: Location.none,
    });
  };
  open Graphql_printer;
  let generate_expr = (acc, part) =>
    switch (acc, part) {
    | (acc, Empty) => acc
    | (None, String(s)) => Some(make_string(s))
    | (Some(acc), String(s)) => Some(join(acc, make_string(s)))
    | (None, FragmentNameRef(f)) => Some(make_fragment_name(f))
    | (Some(acc), FragmentNameRef(f)) =>
      Some(join(acc, make_fragment_name(f)))
    | (None, FragmentQueryRef(f)) => Some(make_fragment_query(f))
    | (Some(acc), FragmentQueryRef(f)) =>
      Some(join(acc, make_fragment_query(f)))
    };

  let result = parts |> Array.fold_left(generate_expr, None);

  switch (result) {
  | None => make_string("")
  | Some(e) => e
  };
};

let rec emit_json =
  Ast_406.(
    fun
    | `Assoc(vs) => {
        let pairs =
          Ast_helper.(
            Exp.array(
              vs
              |> List.map(((key, value)) =>
                   Exp.tuple([
                     Exp.constant(Pconst_string(key, None)),
                     emit_json(value),
                   ])
                 ),
            )
          );
        %expr
        Js.Json.object_(Js.Dict.fromArray([%e pairs]));
      }
    | `List(ls) => {
        let values = Ast_helper.Exp.array(List.map(emit_json, ls));
        %expr
        Js.Json.array([%e values]);
      }
    | `Bool(true) => [%expr Js.Json.boolean(true)]
    | `Bool(false) => [%expr Js.Json.boolean(false)]
    | `Null => [%expr Obj.magic(Js.Undefined.empty)]
    | `String(s) => [%expr
        Js.Json.string([%e Ast_helper.Exp.constant(Pconst_string(s, None))])
      ]
    | `Int(i) => [%expr
        Js.Json.number(
          [%e
            Ast_helper.Exp.constant(Pconst_float(string_of_int(i), None))
          ],
        )
      ]
    | `StringExpr(parts) => [%expr
        Js.Json.string([%e emit_printed_query(parts)])
      ]
  );

let make_printed_query = (config, document) => {
  let source = Graphql_printer.print_document(config.schema, document);
  let reprinted =
    switch (Ppx_config.output_mode()) {
    | Ppx_config.Apollo_AST =>
      Ast_serializer_apollo.serialize_document(source, document) |> emit_json
    | Ppx_config.String =>
      Ast_406.(
        Ast_helper.(
          switch (config.template_literal) {
          | None => emit_printed_query(source)
          | Some(template_literal) =>
            // if the template literal is: "graphql"
            // a string is created like this: graphql`[query]`
            let tmp =
              emit_printed_query(
                ~strProcess=str => template_literal ++ "`\n" ++ str ++ "`",
                source,
              );

            // the only way to emit a template literal for now, using thebs.raw
            // extension
            Exp.extension((
              {txt: "bs.raw", loc: Location.none},
              PStr([
                {pstr_desc: Pstr_eval(tmp, []), pstr_loc: Location.none},
              ]),
            ));
          }
        )
      )
    };

  [[%stri let query = [%e reprinted]]];
};

let generate_default_operation =
    (config, variable_defs, has_error, operation, res_structure) => {
  let parse_fn =
    Output_bucklescript_parser.generate_parser(config, res_structure);
  let types = Output_bucklescript_types.generate_types(config, res_structure);
  let arg_types =
    Output_bucklescript_types.generate_arg_types(config, variable_defs);
  let extracted_args = extract_args(config, variable_defs);
  let serialize_variable_functions =
    Output_bucklescript_serializer.generate_serialize_variables(
      config,
      extracted_args,
    );

  if (has_error) {
    [[%stri let parse = value => [%e parse_fn]]];
  } else {
    let variable_constructors =
      Output_bucklescript_serializer.generate_variable_constructors(
        config,
        extracted_args,
      );
    List.concat([
      make_printed_query(config, [Graphql_ast.Operation(operation)]),
      List.concat([
        [[%stri type raw_t]],
        [types],
        switch (extracted_args) {
        | [] => []
        | _ => [arg_types]
        },
        [[%stri let parse: Js.Json.t => t = value => [%e parse_fn]]],
        switch (serialize_variable_functions) {
        | None => [[%stri let serializeVariables = _ => Js.Json.null]]
        | Some(f) => [f]
        },
        switch (variable_constructors) {
        | None => [[%stri let makeVar = (~f, ()) => f(Js.Json.null)]]
        | Some(c) => [c]
        },
        [
          [%stri let makeVariables = makeVar(~f=f => f)],
          [%stri
            let make =
              makeVar(~f=variables => {
                {"query": query, "variables": variables, "parse": parse}
              })
          ],
          [%stri
            let makeWithVariables = variables => {
              "query": query,
              "variables": serializeVariables(variables),
              "parse": parse,
            }
          ],
          [%stri let definition = (parse, query, makeVar)],
          // [%stri let definition = [%e definition_tuple]],
        ],
      ]),
    ]);
  };
};

let generate_fragment_module =
    (config, name, _required_variables, has_error, fragment, res_structure) => {
  let parse_fn =
    Output_bucklescript_parser.generate_parser(config, res_structure);
  let types = Output_bucklescript_types.generate_types(config, res_structure);

  let variable_names =
    find_variables(config, [Graphql_ast.Fragment(fragment)])
    |> StringSet.elements;

  let variable_fields =
    variable_names
    |> List.map(name =>
         Otag(
           {txt: name, loc: Location.none},
           [],
           Ast_helper.Typ.constr(
             {txt: Longident.Lident("unit"), loc: Location.none},
             [],
           ),
         )
       );
  let variable_obj_type =
    Ast_helper.Typ.constr(
      {txt: Longident.parse("Js.t"), loc: Location.none},
      [Ast_helper.Typ.object_(variable_fields, Open)],
    );
  let contents =
    if (has_error) {
      [
        [%stri
          let make = (_vars: [%t variable_obj_type], value) => [%e parse_fn]
        ],
      ];
    } else {
      List.concat([
        make_printed_query(config, [Graphql_ast.Fragment(fragment)]),
        [
          types,
          [%stri type raw_t],
          Ast_helper.(
            Str.type_(
              Recursive,
              [
                Type.mk(
                  ~manifest=
                    Typ.constr(
                      {loc: Location.none, txt: Longident.Lident("t")},
                      [],
                    ),
                  {
                    loc: Location.none,
                    txt: "t_" ++ fragment.item.fg_type_condition.item,
                  },
                ),
              ],
            )
          ),
          [%stri let parse: Js.Json.t => t = value => [%e parse_fn]],
          [%stri
            let name = [%e
              Ast_helper.Exp.constant(Pconst_string(name, None))
            ]
          ],
        ],
      ]);
    };

  let m =
    Pstr_module({
      pmb_name: {
        txt: Generator_utils.capitalize_ascii(name),
        loc: Location.none,
      },
      pmb_expr: Mod.structure(contents),
      pmb_attributes: [],
      pmb_loc: Location.none,
    });

  [{pstr_desc: m, pstr_loc: Location.none}];
};

let generate_operation = config =>
  fun
  | Mod_default_operation(vdefs, has_error, operation, structure) =>
    generate_default_operation(config, vdefs, has_error, operation, structure)
  | Mod_fragment(name, req_vars, has_error, fragment, structure) =>
    generate_fragment_module(
      config,
      name,
      req_vars,
      has_error,
      fragment,
      structure,
    );

let generate_modules = (config, operations) => {
  let generated = List.map(generate_operation(config), operations);
  Mod.mk(Pmod_structure(List.concat(generated)));
};
