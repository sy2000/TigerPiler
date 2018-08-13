
signature SEMANT =
sig
	val transProg : Absyn.exp -> unit
end 

structure Semant :> SEMANT = struct
	structure A = Absyn
	structure E = Env
	structure P = PrintAbsyn
	structure S = Symbol
	structure T = Types
	structure Tr = Translate
	exception SemantErrorMsg

	type venv = E.enventry S.table
	type tenv = T.ty S.table

  	fun type_to_string(T.ARRAY(typ, uniq)) = "arr " ^ type_to_string(typ)
    | type_to_string(T.INT) = "int"
    | type_to_string(T.NAME(sym, typOpt)) = "name " ^ S.name(sym)
	| type_to_string(T.NIL) = "nil"
    | type_to_string(T.STRING) = "str"
    | type_to_string(T.RECORD(flds, uniq)) = "rec "
    | type_to_string(T.UNIT) = "unit"

	fun type_exists (tenv, n, pos) = 
	let 
		val ret=S.look (tenv, n)
	in
		(case ret of
			SOME ty2 => ty2
			| NONE => (
				ErrorMsg.error pos ("did not find type " ^ S.name n) ; 
				Types.UNIT
			)
		)
	end

	fun checkInt ({exp, ty}, pos) = 
		case ty of
			T.INT => ()
			| _ => ErrorMsg.error pos "expected int!"

	fun checkString ({exp, ty}, pos) = 
		case ty of
			T.STRING => ()
			| _ => ErrorMsg.error pos "expected string!"

	fun checkUnit ({exp, ty}, pos) = 
		case ty of
			T.UNIT => ()
			| _ => ErrorMsg.error pos "expected unit!"

	fun exps_same_type ({exp=exp1,ty=type1}, {exp=exp2,ty=type2}, pos) =
		if type1 = type2 then 
			()
		else 
			ErrorMsg.error pos ("exps_same_type: Expressions are not the same type")

	fun same_type (type1, type2, pos) =
		(case type1 = type2 of
			true => true
			| false => (
				ErrorMsg.error pos ("same_type: false");
				false
			)
		)

  	(* this function tests whether the given type can be used as an argument for an =<> operation *)
  	fun type_can_be_tested_for_equality({exp, ty}, pos) = 
		case ty of 
			Types.INT => ()
			| Types.RECORD(flds, uniq) => ()
			| Types.ARRAY(typ, uniq) => ()
			| Types.NIL => ()
			| _ => (
				ErrorMsg.error pos ("type_can_be_tested_for_equality: not int/record/array");
				()
			)

	(* this function allows comparison operand between two ints, or two strings, all other variations are an error*)
	fun checkOpCompare ({exp=_, ty=T.INT}, {exp=_, ty=T.INT}, pos) = ()
		| checkOpCompare ({exp=_, ty=T.STRING}, {exp=_, ty=T.STRING}, pos) = ()
		| checkOpCompare ({exp=_, ty=_ }, {exp=_, ty=_ }, pos) = ErrorMsg.error pos "checkOpCompare error: types incompatible"

	(* this function allows EQ or NEQ operand between two types. could be ints, string, records, arrays, etc.  can also be compared to nil!
		all otehr variations are an error*)
	fun checkOpEq ({exp=_, ty=T.INT}, {exp=_, ty=T.INT}, pos) = ()
      | checkOpEq ({exp=_, ty=T.STRING}, {exp=_, ty=T.STRING}, pos) = ()
      | checkOpEq ({exp=_, ty=T.ARRAY(_, r1)}, {exp=_, ty=T.ARRAY(_, r2)}, pos) = 
			if r1 = r2 then 
				() 
			else 
				ErrorMsg.error pos "checkOpEq error : eq/neq array mismatch"
      | checkOpEq ({exp=_, ty=T.RECORD(_, r1)}, {exp=_, ty=T.RECORD(_, r2)}, pos) = 
			if r1 = r2 then 
				() 
			else 
				ErrorMsg.error pos "checkOpEq error : eq/neq record mismatch"
      | checkOpEq ({exp=_, ty=T.NIL}, {exp=_, ty=T.RECORD(_, _)}, pos) = ()
      | checkOpEq ({exp=_, ty=T.RECORD(_, _)}, {exp=_, ty=T.NIL}, pos) = ()
      | checkOpEq ({exp=_, ty=_}, {exp=_, ty=_}, pos) = 
		  	ErrorMsg.error pos "checkOpEq error : eq/neq mismatch"

	fun actual_ty(ty) =
		case ty of 
			T.NIL => T.NIL
			| T.RECORD(recs, uniq) => T.RECORD(recs, uniq)
			| T.ARRAY(typ, uniq) => actual_ty(typ)
			| T.UNIT => T.UNIT
			| T.INT => T.INT
			| T.STRING => T.STRING
			| T.NAME(sym, typOpt) => (
				case !typOpt of 
					NONE => T.UNIT
					| SOME(typ) => actual_ty(typ)
			)

	fun my_transTy (tenv, t)=
	let
	in
		print ("my_TransTy: ...\n");
		case t of
			A.NameTy (n, pos) => (
				print ("inside my_transTy, t=NameTy\n");				
				()
			)
			| A.RecordTy fields => (
				print ("inside my_transTy, t=RecordTy\n");
				()
			)
			| A.ArrayTy (n,pos) => (
				print ("inside my_transTy, t=ArrayTy\n");
				()
			)
	end



	fun transTy (tenv, t)=
	let
		fun record_types(fields)= 
			map (
				fn{name, escape, typ, pos}=> (
					case SOME(type_exists(tenv, typ, pos)) of
						SOME t => (name, t)
						| NONE => (name, Types.UNIT)
				)
			) fields
		fun checkdups(h::l) = (
			List.exists (
				fn {name, escape, typ, pos}=> 
				if (#name h)=name then
					(ErrorMsg.error pos ("duplicate field: " ^ Symbol.name name);
					true)
				else
					false) l;
			checkdups(l))
		| checkdups(_) = ()
	in
		print ("TransTy: ...\n");
		case t of
			A.NameTy (n, pos) => 
				type_exists(tenv, n, pos)
			| A.RecordTy fields => (
				checkdups(fields);
				T.RECORD (record_types fields, ref())
			)
			| A.ArrayTy (n,pos) => 
				T.ARRAY(type_exists(tenv, n, pos), ref())
	end

	fun transExp(venv, tenv, exp)  =    
	let 
		fun trexp (A.NilExp) = {exp=Tr.nilExp(), ty=T.NIL}
		| trexp (A.IntExp i) = {exp=Tr.nilExp(), ty=T.INT}
		| trexp (A.StringExp (str, pos)) = {exp=Tr.nilExp(), ty=T.STRING}
		| trexp (A.VarExp var) = trvar var
		| trexp (A.OpExp {left, oper, right, pos}) =
			if oper=A.PlusOp orelse oper=A.MinusOp orelse oper=A.TimesOp orelse oper=A.DivideOp then (
				print " trexp (A.OpExp 1\n"; 
				checkInt(trexp left, pos);
				checkInt(trexp right, pos);
				{exp=(), ty=T.INT}
			) else if oper = A.EqOp orelse oper = A.NeqOp then (
				print "A.EqOp\n";
				checkOpEq(trexp left, trexp right, pos);
				{exp=(), ty=T.INT}
			) else if oper = A.LtOp orelse oper = A.LeOp orelse oper = A.GtOp orelse oper = A.GeOp then (
				print " trexp (A.OpExp 2\n"; 
				checkOpCompare(trexp left, trexp right, pos);
				{exp=(), ty=T.INT}
			) else (
				ErrorMsg.error pos "OpExp failed\n"; {exp=Tr.nilExp(), ty=T.INT}
			)
			
		| trexp (A.IfExp {test, then', else', pos}) = (* TODO *)
			(case else' of
				NONE => 
				let
					val my_test = trexp(test)
					val my_then = trexp(then')
				in 
					print ("A.IfExp... NONE else'\n"); 
					checkInt(my_test, pos);
					checkUnit(my_then, pos);
					{exp=Tr.nilExp(), ty=T.UNIT}
				end
				| SOME else' =>
				let
					val my_test = trexp(test)
					val my_then = trexp(then')
					val my_else = trexp(else')
				in
					print ("A.IfExp... SOME else'\n"); 
					checkInt(my_test, pos);
					checkUnit(my_then, pos);
					exps_same_type(my_then, my_else, pos);
					{exp=Tr.nilExp(), ty=T.UNIT}
				end		
			)
		| trexp (A.SeqExp exps) 							=
		let 
			fun parse_sequence_expressions [] = {exp=(), ty=Types.UNIT}
                | parse_sequence_expressions ((exp, pos)::nil) = trexp exp
                | parse_sequence_expressions ((exp, pos)::rst) = (trexp exp; parse_sequence_expressions rst)
		in
			print ("A.SeqExp...\n");
			parse_sequence_expressions(exps)
		end
		| trexp (A.CallExp {func, args, pos})				= 
		let
			fun check_args([], [], pos) = ()
			| check_args(formals, [], pos) = ErrorMsg.error pos "too few args"
			| check_args([], args, pos) = ErrorMsg.error pos "too much args"
			| check_args(formal::formals, arg::args, pos) = 
			(
				let 
					val {exp, ty} = trexp arg
				in 
					if formal = ty then 
						()
					else 
						ErrorMsg.error pos (S.name(func) ^ ": wrong type arg")
				end;
				check_args(formals, args, pos)
			)
		in
			print ("A.CallExp...\n");
			(case S.look(venv, func) of 
				NONE => (
					ErrorMsg.error pos ("NONE expression is not a function :" ^ S.name(func));
					{exp=(), ty=Types.UNIT}
				)
				| SOME(E.FunEntry {formals, result}) => (
					check_args(formals, args, pos);
					{exp=(), ty=actual_ty(result)}
				)
				| _ => (
					ErrorMsg.error pos ("_ unknown function " ^ S.name(func));
					{exp=(), ty=Types.UNIT}
				)
			)
		end

		| trexp (A.WhileExp {test, body, pos}) 				= 
		let
			val my_test = trexp test
			val my_body = trexp body
		in  (* TODO nesting? *)
			checkInt(my_test, pos);
			checkUnit(my_body, pos);
			{exp=(), ty=Types.UNIT}
		end
		| trexp (A.LetExp {decs, body, pos}) 				=
		let 
			val {venv=venv', tenv=tenv'} = transDecs(venv, tenv, decs)
		in
			print ("A.LetExp...\n"); 
			transExp(venv', tenv', body)
		end
		| trexp (A.RecordExp {fields, typ, pos}) 			= 
		let 
			val my_type_exists = type_exists(tenv, typ, pos)
			val result = actual_ty my_type_exists
			val field_names = map #1 fields
			val fields_types = map trexp (map #2 fields)
			val actual_types = map #ty fields_types
		in 
			print ("A.RecordExp...\n"); 
			case result of
				T.RECORD(my_symbol, my_unique) =>
				let 
					val found_field_names = map #1 my_symbol
					val found_field_types = map actual_ty (map #2 my_symbol)
				in
					if field_names = found_field_names then 
						if (ListPair.all
								(fn (ty1, ty2) => same_type (ty1, ty2, pos))
								(actual_types, found_field_types)) then
							{exp=Tr.nilExp(), ty=T.RECORD(my_symbol,my_unique)} 
						else (
							ErrorMsg.error pos ("field types not consistent: " ^ S.name typ);
							{exp=Tr.nilExp(),ty=T.RECORD(my_symbol,my_unique)}
						)
					else (
						ErrorMsg.error pos ("field types not consistent: " ^ S.name typ);
						{exp=Tr.nilExp(),ty=T.RECORD(my_symbol,my_unique)}
					)
				end
				| _ => (
					ErrorMsg.error pos ("not a valid record type: " ^ S.name typ);
					{exp=Tr.nilExp(), ty=T.UNIT}
				)
		end

		| trexp (A.AssignExp {var, exp, pos}) 				= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.ForExp {var, escape, lo, hi, body, pos}) = {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.BreakExp pos) 							= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.ArrayExp {typ, size, init, pos}) 		= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		and
		trvar (A.SimpleVar(id,pos)) = 
			(case S.look(venv, id) of
				SOME (E.VarEntry{ty}) => {exp=Tr.nilExp(), ty=T.INT}
				| _ => (
					ErrorMsg.error pos ("var undefined... " ^ S.name id); 
					{exp=Tr.nilExp(), ty=T.INT}
				)
			)
		| trvar (A.FieldVar(var,id,pos)) =
		let
			val var' = trvar var
		in
			(case var' of
				{exp, ty=record as T.RECORD (fields, _)} => {exp=Tr.nilExp(), ty=record}
				| _ => (ErrorMsg.error pos "var not found"; {exp=Tr.nilExp(), ty=T.UNIT})
			)
		end
		| trvar (A.SubscriptVar(var, exp,pos)) = (
			checkInt(trexp exp, pos);
			{exp=Tr.nilExp(), ty=T.UNIT}
		)
    in
		print ("transExp body...\n");
		trexp(exp)
    end

	and

	transDec (venv, tenv, A.VarDec{name, typ=NONE, init,... }) = 
	(* first case is a simple declaration, like "var a:=0" *)
	let
		val {exp,ty} = transExp (venv, tenv, init)
	in
		print ("inside transDec A.VarDec typ=NONE...\n");
		{tenv = tenv, venv=S.enter(venv, name, E.VarEntry{ty=ty})}
	end
	(* next case is a case where a type is present, like "var a:int := 6", so we need to check the constraint and init expression are compatible *)
	| transDec (venv, tenv, A.VarDec{name,escape,typ=SOME(symb, pos), init, pos=pos1}) =
	let
		val {exp, ty} = transExp (venv, tenv, init)
	in
		print ("inside transDec, A.VarDec ,typ=SOME(symb, pos)...\n");

		(case S.look (tenv,symb) of
			NONE => (
				ErrorMsg.error pos ("type not defined: " ^ S.name symb);
				{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})}
			)
			| SOME my_ty=>  
				if ty<>my_ty then (
					ErrorMsg.error pos "type mismatch" ;
					{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})} 
				) else (
					();
					{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})} 
				)
		)

	end
	| transDec (venv, tenv, A.TypeDec type_decs) = 
	let
		val type_types = map #ty type_decs
		val type_names = map #name type_decs
		val first_type = List.hd type_types
		val first_name = List.hd type_names
		val nts = map (fn t => my_transTy (tenv, t)) type_types
	in
		(case first_type of
			NameTy => (
				print ("inside transDec, A.TypeDec ,first type=NameTy\n");
				print ("first_name=" ^ (S.name first_name) ^ "\n");
				{tenv=tenv, venv=venv}
			)
			(*
			| RecordTy => (
				print ("inside transDec, A.TypeDec ,first type=RecordTy");
				{tenv=tenv, venv=venv}
			)
			| ArrayTy => (
				print ("inside transDec, A.TypeDec ,first type=ArrayTy");
				{tenv=tenv, venv=venv}
			)
			*)
			(*
			| _ => (
				print ("inside transDec, A.TypeDec ,first type=_");
				{tenv=tenv, venv=venv}
			)
			*)
		)
	end

(*
   | transDec (venv, tenv, A.TypeDec type_decs) = 
          let
            val type_names = map #name type_decs
            val type_types = map #ty type_decs

            fun add_type (new_type, env) = 
				S.enter(env, new_type, T.NAME(new_type,ref(S.look(tenv, new_type))))

            val tenv' = foldr add_type tenv type_names
            val nts = map (fn t => transTy (tenv', t)) type_types

            fun update_type (n,nt) = 
			let 
				val (SOME (T.NAME(_,r))) = S.look(tenv',n)
			in 
				r := SOME nt
            end
            val _ = app update_type (ListPair.zip(type_names,nts))
            in
				print ("transDec A.TypeDec \n");
                {tenv=tenv', venv=venv}
            end
*)
(*
	| transDec(venv, tenv, A.TypeDec typeDecs) =
	let
		fun updateDecs (venv, tenv) =
		let
			fun update_TypeDec {name, ty, pos} = 
			let
				fun lookupType(pos, tenv, ty) =
					case S.look(tenv, ty) of 
						SOME ty => ty
						(*
						| NONE => (
							ErrorMsg.error pos ("Type '" ^ S.name ty ^ "' is not defined"); 
							T.NIL
						)
						*)
						| _ =>  (
							ErrorMsg.error pos ("Type '" ^ S.name ty ^ "' is neither SOME nor NONE"); 
							T.NIL
						)
				val T.NAME(tyName, tyRef) = lookupType (pos, tenv, name)
				val ty = case ty of 
					A.NameTy (name, pos) => 
						T.NAME (name, ref (SOME (lookupType (pos, tenv, name))))
						| A.RecordTy fields => 
							T.RECORD (map (fn ({name, escape, typ, pos}) => (name, lookupType (pos, tenv, typ))) fields, ref ())
						| A.ArrayTy (name, pos) => 
							T.ARRAY (lookupType (pos, tenv, name), ref ())
			in
				tyRef := SOME(ty)
			end
		in
			app update_TypeDec typeDecs
		end

		fun enterTypeHeader ({name, ty, pos}, tenv) = S.enter (tenv, name, T.NAME (name, ref NONE))
		val tenv' = foldl enterTypeHeader tenv typeDecs
	in
		updateDecs (venv, tenv');
		{tenv=tenv', venv=venv}
	end
*)
	| transDec(venv, tenv, A.FunctionDec[{name, params, body, pos, result=SOME(rt,pos1)}]) = 
		(print ("transDec A.FunctionDec \n"); {tenv=tenv, venv=venv} ) (* TODO *)
	| transDec(venv, tenv, _) = 
		(print ("transDec _ \n"); {tenv=tenv, venv=venv} ) (* TODO *)


	and 
	transDecs(venv, tenv, []) = {venv=venv, tenv=tenv}
	| transDecs(venv, tenv, dec::decs) =
	let 
		val {tenv=tenv', venv=venv'} = transDec(venv, tenv, dec)
	in 
		transDecs(venv', tenv', decs)
	end


	fun transProg(my_exp: A.exp) = (
		PrintAbsyn.print(TextIO.stdOut, my_exp); 
		transExp(E.base_venv, E.base_tenv, my_exp);
		()
	)
end
