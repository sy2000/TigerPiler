
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

	fun print_actual_ty(ty) =
		case ty of 
			T.NIL => (
				print("******************* print_actual_ty ty=T.NIL\n");
				T.NIL
			)
			| T.RECORD(recs, uniq) => (
				print("******************* print_actual_ty ty=T.RECORD\n");
				T.RECORD(recs, uniq)
			)
			| T.ARRAY(typ, uniq) => (
				print("******************* print_actual_ty ty=T.ARRAY\n");
				print_actual_ty(typ);
				T.ARRAY(typ, uniq)				
			)
			| T.UNIT => ( 
				print("******************* print_actual_ty ty=T.UNIT\n");
				T.UNIT
			)
			| T.INT => (
				print("******************* print_actual_ty ty=T.INT\n");
				T.INT
			)
			| T.STRING => (
				print("******************* print_actual_ty ty=T.STRING\n");
				T.STRING
			)
			| T.NAME(sym, typOpt) => (
				case !typOpt of 
					NONE => (
						print("******************* print_actual_ty ty=T.UNIT\n");
						T.UNIT
					)
					| SOME(typ) => print_actual_ty(typ)
			)


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
			| _ => (
				print_actual_ty(ty);
				ErrorMsg.error pos "expected int!"
			)

	fun checkString ({exp, ty}, pos) = 
		case ty of
			T.STRING => ()
			| _ => ErrorMsg.error pos "expected string!"

	fun checkUnit ({exp, ty}, pos) = 
		case ty of
			T.UNIT => ()
			| _ => (
				print_actual_ty(ty);
				ErrorMsg.error pos "expected unit!"
			)

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


	fun find_actual_type(pos, tenv, my_type) =
		case S.look (tenv, my_type) of
			NONE => (
				ErrorMsg.error pos ("type not defined: " ^ S.name my_type);
				T.NIL
			)
			| SOME found_type =>  (
				print ("******************* find_actual_type: found my_type= " ^ S.name my_type ^ "\n");
				print_actual_ty(found_type)
				(* found_type *)
			)

	fun compare_actual_types(type1, type2) = (
	let
		val found_type1 = print_actual_ty(type1);
		val found_type2 = print_actual_ty(type2);
	in
		print("******************* compare_actual_types: printed both types...\n");
		case found_type1 of 
			T.ARRAY(base_type1, uniq1) => (
				print("******************* compare_actual_types: type1 is an array\n");
				case found_type2 of
					T.ARRAY(base_type2, uniq2) => (
						print("******************* compare_actual_types: type2 is an array\n");
						if actual_ty(base_type1) <> actual_ty(base_type2) then
							T.NIL
						else
							actual_ty(base_type1)
					)
					| _ => (
						print("******************* compare_actual_types: type2 is NOT an array\n");
						T.NIL
					)
			)
			| _ => (
				case found_type2 of
					T.ARRAY(base_type2, uniq2) => 
						T.NIL
					| _ => (
						if actual_ty(type1) <> actual_ty(type2) then
							T.NIL
						else (
							print("******************* compare_actual_types: not an array but types match!\n");
							actual_ty(type1)
						)
					)
			)
	end
	)

	fun my_transTy (tenv, t)=
	let
	in
		print ("******************* my_TransTy: ...\n");
		case t of
			A.NameTy (n, pos) => (
				print ("******************* inside my_transTy, t=NameTy\n");				
				()
			)
			| A.RecordTy fields => (
				print ("******************* inside my_transTy, t=RecordTy\n");
				()
			)
			| A.ArrayTy (n,pos) => (
				print ("******************* inside my_transTy, t=ArrayTy\n");
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
		print ("******************* TransTy: ...\n");
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
				print "******************* trexp (A.OpExp 1\n"; 
				checkInt(trexp left, pos);
				checkInt(trexp right, pos);
				{exp=(), ty=T.INT}
			) else if oper = A.EqOp orelse oper = A.NeqOp then (
				print "******************* A.EqOp\n";
				checkOpEq(trexp left, trexp right, pos);
				{exp=(), ty=T.INT}
			) else if oper = A.LtOp orelse oper = A.LeOp orelse oper = A.GtOp orelse oper = A.GeOp then (
				print "******************* trexp (A.OpExp 2\n"; 
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
					print ("******************* A.IfExp... NONE else'\n"); 
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
					print ("******************* A.IfExp... SOME else'\n"); 
					checkInt(my_test, pos);
					(* checkUnit(my_then, pos); *)
					exps_same_type(my_then, my_else, pos);
					{exp=Tr.nilExp(), ty=(#ty my_then)}
				end		
			)
		| trexp (A.SeqExp exps) 							=
		let 
			fun parse_sequence_expressions [] = {exp=(), ty=Types.UNIT}
                | parse_sequence_expressions ((exp, pos)::nil) = trexp exp
                | parse_sequence_expressions ((exp, pos)::rst) = (trexp exp; parse_sequence_expressions rst)
		in
			print ("******************* A.SeqExp...\n");
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
			print ("******************* A.CallExp...\n");
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
			print ("******************* A.LetExp...\n"); 
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
			print ("******************* A.RecordExp...\n"); 
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

		| trexp (A.AssignExp {var, exp, pos}) 				= 
		let
			val  {exp=left,  ty=lefthand_type} = trvar (var)
			val  {exp=right, ty=righthand_type} = trexp (exp)
		in
			print("******************* trexp A.AssignExp...\n");
			if lefthand_type <> righthand_type then (
				print_actual_ty(lefthand_type);
				print_actual_ty(righthand_type);
				ErrorMsg.error pos ("trexp A.AssignExp error: lefthand_type <> righthand_type");
				{exp=Tr.nilExp(), ty=T.UNIT}
			) else
				{exp=(), ty=T.UNIT} 
		end
		| trexp (A.ForExp {var, escape, lo, hi, body, pos}) = 
		let
			val translated_lo = trexp lo
			val translated_hi = trexp hi
			val translated_body = transExp (venv, tenv, body)
		in
			print("******************* trexp A.ForExp...\n");
			checkInt(translated_lo, pos);
			checkInt(translated_hi, pos);
			checkUnit(translated_body, pos);
			{exp=Tr.nilExp(), ty=T.UNIT} (* TODO *)
		end
		| trexp (A.BreakExp pos) 							= 
		let
		in
			print("******************* trexp A.BreakExp...\n");
			{exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		end
		| trexp (A.ArrayExp {typ, size, init, pos}) 		= 
		let
			val array_type = find_actual_type(pos, tenv, typ)
		in
			print("******************* trexp A.ArrayExp...\n");
			case array_type of
				T.ARRAY(typ, uniq) => (
					print("******************* found array_type of type \n");
					{exp=Tr.nilExp(), ty=T.ARRAY(typ, uniq)} (* TODO *)
				)
				| _  => (					
					print("******************* did not find an array_type\n");
					print_actual_ty(array_type);					
					{exp=Tr.nilExp(), ty=T.NIL} (* TODO *)
				)
			
			
		end

		and
		trvar (A.SimpleVar(id,pos)) = 
			(
				print("******************* trvar (A.SimpleVar\n");
				case S.look(venv, id) of
				SOME (E.VarEntry{ty}) => (
					print_actual_ty(ty);
					{exp=Tr.nilExp(), ty=actual_ty(ty)}
				)
				| _ => (
					ErrorMsg.error pos ("var undefined... " ^ S.name id); 
					{exp=Tr.nilExp(), ty=T.INT}
				)
			)
		| trvar (A.FieldVar(var,id,pos)) =
		let
			val var' = trvar var
		in
			(
				print("******************* trvar (A.FieldVar\n");
				print_actual_ty(#ty var');
				case var' of
				{exp, ty=record as T.RECORD (fields, _)} => (
					case List.find (fn (fSym, fTy) => fSym = id) fields of 
						SOME(found_symbol, found_type) => (
							print_actual_ty(found_type);
							{exp=Tr.nilExp(), ty=actual_ty (found_type)}
						)
						| NONE => (
							ErrorMsg.error pos ("field " ^ S.name id ^ " does not exist"); 
							{exp=Tr.nilExp(), ty=T.UNIT}
						)
            	)
				| _ => (
					ErrorMsg.error pos ("var not found ") ; 
					{exp=Tr.nilExp(), ty=T.UNIT}
				)
			)
		end
		| trvar (A.SubscriptVar(var, exp,pos)) = (
			print("******************* trvar (A.SubscriptVar\n");
			checkInt(trexp exp, pos);
			{exp=Tr.nilExp(), ty=T.UNIT}
		)
    in
		print ("******************* transExp body...\n");
		trexp(exp)
    end
	and
	transDec (venv, tenv, A.VarDec{name, typ=NONE, init,... }) = 
	(* first case is a simple declaration, like "var a:=0" *)
	let
		val {exp,ty} = transExp (venv, tenv, init)
	in
		print ("******************* inside transDec A.VarDec typ=NONE...\n");
		{tenv = tenv, venv=S.enter(venv, name, E.VarEntry{ty=ty})}
	end
	(* next case is a case where a type is present, like "var a:int := 6", so we need to check
	   the constraint and init expression are compatible *)
	| transDec (venv, tenv, A.VarDec{name,escape,typ=SOME(symb, pos), init, pos=pos1}) =
	let
		val {exp, ty} = transExp (venv, tenv, init)
	in
		print ("******************* inside transDec, A.VarDec ,typ=SOME(symb, pos)...\n");
		(case S.look (tenv,symb) of
			NONE => (
				ErrorMsg.error pos ("type not defined: " ^ S.name symb);
				{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})}
			)
			| SOME my_ty=>  
				if compare_actual_types(ty,my_ty) = T.NIL then (
					ErrorMsg.error pos ("type mismatch symb=" ^ S.name symb);
					print("******************* showing actual type for ty...\n");
					print_actual_ty(ty);
					print("******************* showing actual type for the found my_ty...\n");
					print_actual_ty(my_ty);
					{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})} 
				) else (
					print("******************* variable declaration successful, added var " ^ S.name name ^ "\n");
					{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})} 
				)
		)
	end

	| transDec(venv, tenv, A.TypeDec typeDecs) =
	let
		fun updateDecs_for_venv (venv, tenv) =
		let
			fun updateDec_for_name_type {name, ty, pos} = 
			let
				fun find_type(pos, tenv, ty) =
					case S.look(tenv, ty) of 
						SOME ty => (
							print ("******************* inside find_type, A.TypeDec ,S.look(tenv, ty) is SOME ty\n");
							ty
						)
						| NONE   => (
							ErrorMsg.error pos ("Type '" ^ S.name ty ^ "' is not defined"); 
							T.NIL
						)
				val T.NAME(tyName, tyRef) = find_type (pos, tenv, name)
				val ty = case ty of 
					A.NameTy (name, pos) => (
						(* TODO - test it is working *)
						print ("******************* 1 inside updateDec_for_name_type, A.TypeDec ,S.look(tenv, ty) is SOME ty\n");
						T.NAME (name, ref (SOME (find_type (pos, tenv, name))))
					)
					| A.RecordTy fields => (
						(* TODO - test it is working *)
						print ("******************* 2 inside updateDec_for_name_type, A.TypeDec ,S.look(tenv, ty) is SOME ty\n");
						T.RECORD (map (fn ({name, escape, typ, pos}) => (name, find_type (pos, tenv, typ))) fields, ref ())
					)
					| A.ArrayTy (name, pos) => (
						print ("******************* inside updateDec_for_name_type, A.TypeDec ,case ty of A.ArrayTy, name=" ^ S.name name ^ "\n");
						T.ARRAY (find_type (pos, tenv, name), ref ())
					)
			in
				print_actual_ty(ty);
				tyRef := SOME(ty)
			end
		in
			app updateDec_for_name_type typeDecs (* applies updateDec_for_name_type to all elements of typeDecs *)
		end
		fun enterTypeHeader ({name, ty, pos}, tenv) = S.enter (tenv, name, T.NAME (name, ref NONE))
		val tenv' = foldl enterTypeHeader tenv typeDecs
		fun find_type_in_new_tenv {name, ty, pos} = (
			print("******************* find_type_in_new_tenv now trying to find name=" ^ S.name name ^ "\n");
			case S.look (tenv', name) of
				NONE => (
					ErrorMsg.error pos ("type not defined: arrtype");
					()
				)
				| SOME my_ty=>  (
					print_actual_ty(my_ty);
					()
				)
		)
		fun find_type_in_old_tenv {name, ty, pos} = (
			print("******************* find_type_in_old_tenv: find_type_in_old_tenv now trying to find name=" ^ S.name name ^ "\n");
			case S.look (tenv, name) of
				NONE => (
					print ("******************* find_type_in_old_tenv: type was not supposed to be defined: " ^ S.name name ^ "\n");
					()
				)
				| SOME my_ty=>  (
					print_actual_ty(my_ty);
					()
				)
		)
	in (* of transDec(venv, tenv, A.TypeDec typeDecs) *)
		updateDecs_for_venv (venv, tenv');
		(* does the new type now exist in tenv` ?  need to verify... this is just to convince myself it is working *)
		print("******************* now trying to find it again...\n");
		(app find_type_in_old_tenv typeDecs);
		(app find_type_in_new_tenv typeDecs);
		{tenv=tenv', venv=venv}
	end

	| transDec(venv, tenv, A.FunctionDec[{name, params, body, pos, result}]) = 
	let
		fun get_result_type(tenv, res) = (
			case res of
				NONE => (
					print("******************* get_result_type: NONE type (procedure)");
					T.UNIT
				)
				| SOME (rt, rt_pos) => (
					print("******************* get_result_type: SOME type...\n");
					find_actual_type(rt_pos, tenv, rt)
				)
		)
		(*fun trans_param {param_name, param_type, pos} = (   *)
		fun trans_param ({name, escape, typ, pos}:Absyn.field) = (
			case S.look(tenv, typ) of
				SOME(found_type) =>
					{name=name, ty=found_type}
				| NONE => (
					ErrorMsg.error pos (" trans_param: type not defined:" ^ S.name typ); 
					{name=name, ty=T.NIL}
				)
		)
		val rt = get_result_type(tenv, result)
		val params_types_list = map trans_param params
		val venv_with_func_header = S.enter(venv, name, E.FunEntry {formals=map #ty params_types_list, result=rt})
		fun enter_param({name, ty}, venv) = S.enter(venv, name, E.VarEntry {ty=ty})
		val venv_body = foldl enter_param venv_with_func_header params_types_list
		val translated_body = transExp(venv_body, tenv, body)
		val body_type = #ty translated_body
	in
		print ("******************* transDec A.FunctionDec \n"); 
		 		
		if body_type <> rt then (
			ErrorMsg.error pos ("transDec A.FunctionDec: body_type <> rt");
			print_actual_ty(body_type);
			print_actual_ty(rt);
			{tenv=tenv, venv=venv}
		) else (
			{tenv=tenv, venv=venv_with_func_header}
		)               
	end

	| transDec(venv, tenv, _) = 
		(print ("******************* transDec _ \n"); {tenv=tenv, venv=venv} ) (* TODO *)


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
