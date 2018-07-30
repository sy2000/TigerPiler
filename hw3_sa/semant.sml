
signature SEMANT =
sig
	val transProg : Absyn.exp -> unit
end 

structure Semant :> SEMANT = struct
	structure A = Absyn
	structure E = Env
	structure P = PrintAbsyn
	structure S = S
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

	fun checkSameType ({expr_arg=exp1,ty=type1}, {expr_arg=exp2,ty=type2}, pos) =
		if type1 = type2 then 
			()
		else 
			ErrorMsg.error pos ("checkSameType: Expressions are not the same type")

  	(* this function tests whether the given type can be used as an argument for an =<> operation *)
  	fun type_can_be_tested_for_equality({exp, ty}, pos) = 
		case ty 
        of Types.INT => ()
         | Types.RECORD(flds, uniq) => ()
         | Types.ARRAY(typ, uniq) => ()
         | Types.NIL => ()
         | _ => (ErrorMsg.error pos ("type_can_be_tested_for_equality: not int/record/array");
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
		case ty
			of T.NIL => T.NIL
			| T.RECORD(recs, uniq) => T.RECORD(recs, uniq)
			| T.ARRAY(typ, uniq) => actual_ty(typ)
			| T.UNIT => T.UNIT
			| T.INT => T.INT
			| T.STRING => T.STRING
			| T.NAME(sym, typOpt) => 
				(case !typOpt
					of NONE => T.UNIT
					| SOME(typ) => actual_ty(typ))

	fun transExp(venv, tenv, exp)  =    
	let 
		fun	trexp (A.NilExp) = {exp=Tr.nilExp(), ty=T.NIL}
		| trexp (A.VarExp var) = trvar var
		| trexp (A.IntExp i) = {exp=Tr.nilExp(), ty=T.INT}
		| trexp (A.StringExp (str, pos)) = {exp=Tr.nilExp(), ty=T.STRING}
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
				(*
					checkInt(my_test);
					checkUnit(my_then);
				*)
					{exp=Tr.nilExp(), ty=T.STRING}
					(*{exp=(Tr.IfThenExp(#exp my_test, #exp my_then)), ty=Types.Unit}*)
				end
			| SOME else' =>
				let
					val my_test = trexp(test)
					val my_then = trexp(then')
					val my_else = trexp(else')
				in
					print ("A.IfExp... SOME else'\n"); 
				(*
					checkInt(my_test);
					checkUnit(my_then);
					checkSameType(my_then, my_else)
				*)
					{exp=Tr.nilExp(), ty=T.STRING}
					(*{exp=(Tr.ifThenElseExp(#exp test', #exp then'', #exp else'')), ty=Types.UNIT}*)
				end		
			)
		(*	
		| trexp (A.IfExp {test, then', else', pos}) 		= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		*)
		| trexp (A.SeqExp exps) 							=
			let 
				fun parse_sequence_expressions [] = {exp=(), ty=Types.UNIT}
                    | parse_sequence_expressions ((exp, pos)::nil) = trexp exp
                    | parse_sequence_expressions ((exp, pos)::rst) = (trexp exp; parse_sequence_expressions rst)
			in
				print ("A.SeqExp...\n");
				parse_sequence_expressions(exps)
				(* {exp=Tr.nilExp(), ty=T.STRING}) (* TODO *) *)
			end
		| trexp (A.CallExp {func, args, pos})				= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.WhileExp {test, body, pos}) 				= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.RecordExp {fields, typ, pos}) 			= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.AssignExp {var, exp, pos}) 				= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.ForExp {var, escape, lo, hi, body, pos}) = {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.BreakExp pos) 							= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		| trexp (A.LetExp {decs, body, pos}) 				= (* {exp=Tr.nilExp(), ty=T.STRING} (* TODO *) *)
 
			let 
				val {venv=venv', tenv=tenv'} = transDecs(venv, tenv, decs)
			in
				print ("A.LetExp...\n"); 
				transExp(venv', tenv', body)
			end

		| trexp (A.ArrayExp {typ, size, init, pos}) 		= {exp=Tr.nilExp(), ty=T.STRING} (* TODO *)
		and
		trvar (A.SimpleVar(id,pos)) = 
			(case S.look(venv, id) of
				SOME (E.VarEntry{ty}) => {exp=Tr.nilExp(), ty=T.INT}
				| _ => (ErrorMsg.error pos ("var undefined... " ^ S.name id); {exp=Tr.nilExp(), ty=T.INT})
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

	| transDec(venv, tenv, A.TypeDec typeDecs) =
		(print ("transDec A.TypeDec \n"); {tenv=tenv, venv=venv} ) (* TODO *)

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
