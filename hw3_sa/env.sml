structure S = Symbol
structure T = Types

(* this signature is taken from the textbook *)
signature ENV = 
sig
  type access
  type ty = T.ty
  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}
  val base_tenv : ty S.table (* predefined types *)
  val base_venv : enventry S.table (* predefined functions *) 
end


structure Env :> ENV = struct
	type access = unit
	type ty = T.ty

 	datatype enventry = VarEntry of {ty: ty}
		| FunEntry of {formals: ty list, result: ty}

	fun my_enter((name, enventry), venv) = S.enter (venv, S.symbol name, enventry)

	val predefined_types = [
		("int", T.INT),
		("string", T.STRING)
	]
	val base_tenv = List.foldr my_enter S.empty predefined_types

	val predefined_funcs = [
		("chr", FunEntry {formals=[T.INT], result=T.STRING}),
		("concat", FunEntry {formals=[T.STRING, T.STRING], result=T.STRING}),
		("exit", FunEntry {formals=[T.INT], result=T.UNIT}),
		("flush", FunEntry {formals=[], result=T.UNIT}),
		("getchar", FunEntry {formals=[], result=T.STRING}),
		("nil", VarEntry {ty=T.NIL}),
		("not", FunEntry {formals=[T.INT], result=T.INT}),
		("ord", FunEntry {formals=[T.STRING], result=T.INT}),
		("print", FunEntry {formals=[T.STRING], result=T.UNIT}),
		("size", FunEntry {formals=[T.STRING], result=T.INT}),
		("substring", FunEntry {formals=[T.STRING, T.INT, T.INT], result=T.STRING})
	]
	val base_venv = List.foldr my_enter S.empty predefined_funcs
end


