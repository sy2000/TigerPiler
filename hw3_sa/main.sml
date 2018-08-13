structure Main = struct
	fun main(argv0: string, arg_list: string list) : int =
	let
		val filename = List.hd arg_list
		val parsed_ast = Parse.parse filename
	in
		Semant.transProg(parsed_ast);
		0 (* return 0 == success to the OS *)
	end
end