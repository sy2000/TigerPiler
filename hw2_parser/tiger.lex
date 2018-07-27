(* Assignment 1: Lexer  						*)
(* Copyright of Amir Shlomo Yaakobovich  		*)

type svalue = Tokens.svalue
type pos = int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token




val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val comment_nesting_level : int ref = ref 0
val last_open_comment_pos : int ref = ref 0
val last_open_string_pos : int ref = ref 0
val inside_string : bool ref = ref false
val raw_string : string ref = ref ""

exception LexFailure


fun eof() = 
	let 
		val pos = hd(!linePos)
	in
		lineNum := 0;
		if (!inside_string = true) then (
			ErrorMsg.error (!last_open_string_pos) ("unclosed string detected at EOF");
			raise LexFailure
		) else if (!comment_nesting_level > 0) then (
            ErrorMsg.error (!last_open_comment_pos) ("unclosed comment detected at EOF");
			raise LexFailure
        ) else ();
		Tokens.EOF(pos,pos)
	end

fun parse_3digits_ascii(s) = Char.toString(chr(valOf(Int.fromString(substring(s,1,size(s)-1)))))

fun check_digits_escape(mytext, pos1, pos2) = 
	let 
		val digit_str = String.substring(mytext,0, 3)
		val digit_num = valOf (Int.fromString digit_str)
	in
		ErrorMsg.error (pos1) ("check_digits_escape: " ^ Int.toString(digit_num));
		if ( digit_num > 127) then (
			ErrorMsg.error (pos1) ("bad escape sequence \\" ^ Int.toString(digit_num) ^" inside string");
			raise LexFailure 
		) else (parse_3digits_ascii(mytext))    
	end


fun match_keyword(mytext, pos1, pos2) =
	if String.compare(mytext,"array") = EQUAL then Tokens.ARRAY(pos1, pos2) else
	if String.compare(mytext,"break") = EQUAL then Tokens.BREAK(pos1, pos2) else
	if String.compare(mytext,"do") = EQUAL then Tokens.DO(pos1, pos2) else
	if String.compare(mytext,"else") = EQUAL then Tokens.ELSE(pos1, pos2) else
	if String.compare(mytext,"end") = EQUAL then Tokens.END(pos1, pos2) else
	if String.compare(mytext,"for") = EQUAL then Tokens.FOR(pos1, pos2) else
	if String.compare(mytext,"function") = EQUAL then Tokens.FUNCTION(pos1, pos2) else
	if String.compare(mytext,"if") = EQUAL then Tokens.IF(pos1, pos2) else
	if String.compare(mytext,"in") = EQUAL then Tokens.IN(pos1, pos2) else
	if String.compare(mytext,"let") = EQUAL then Tokens.LET(pos1, pos2) else
	if String.compare(mytext,"nil") = EQUAL then Tokens.NIL(pos1, pos2) else
	if String.compare(mytext,"of") = EQUAL then Tokens.OF(pos1, pos2) else
	if String.compare(mytext,"then") = EQUAL then Tokens.THEN(pos1, pos2) else
	if String.compare(mytext,"to") = EQUAL then Tokens.TO(pos1, pos2) else
	if String.compare(mytext,"type") = EQUAL then Tokens.TYPE(pos1, pos2) else
	if String.compare(mytext,"var") = EQUAL then Tokens.VAR(pos1, pos2) else
	if String.compare(mytext,"while") = EQUAL then Tokens.WHILE(pos1, pos2) else
	Tokens.ID(mytext, pos1, pos2)




%% 
%header (functor TigerLexFun (structure Tokens: Tiger_TOKENS));
ws=[\t\ ]+;
nl=[\n\r\f]+;
format_char={ws}|{nl};
%s STRINGFOUND TOKENFOUND ESCAPEFOUND FORMAT COMMENTFOUND;

%%


<INITIAL>[a-zA-Z][a-zA-Z0-9_]*  => (match_keyword(yytext, yypos, yypos+size(yytext)));

<INITIAL>"&"               => (Tokens.AND(yypos,yypos+1));
<INITIAL>":="              => (Tokens.ASSIGN(yypos,yypos+2));
<INITIAL>":"               => (Tokens.COLON(yypos,yypos+1));
<INITIAL>","               => (Tokens.COMMA(yypos,yypos+1));
<INITIAL>"/"               => (Tokens.DIVIDE(yypos,yypos+1));
<INITIAL>"."               => (Tokens.DOT(yypos,yypos+1));
<INITIAL>"="               => (Tokens.EQ(yypos,yypos+1));
<INITIAL>">="              => (Tokens.GE(yypos,yypos+2));
<INITIAL>">"               => (Tokens.GT(yypos,yypos+1));
<INITIAL>"{"               => (Tokens.LBRACE(yypos,yypos+1));
<INITIAL>"["               => (Tokens.LBRACK(yypos,yypos+1));
<INITIAL>"<="              => (Tokens.LE(yypos,yypos+2));
<INITIAL>"("               => (Tokens.LPAREN(yypos,yypos+1));
<INITIAL>"<"               => (Tokens.LT(yypos,yypos+1));
<INITIAL>"-"               => (Tokens.MINUS(yypos,yypos+1));
<INITIAL>"<>"              => (Tokens.NEQ(yypos,yypos+2));
<INITIAL>"|"               => (Tokens.OR(yypos,yypos+1));
<INITIAL>"+"               => (Tokens.PLUS(yypos,yypos+1));
<INITIAL>"}"               => (Tokens.RBRACE(yypos,yypos+1));
<INITIAL>"]"               => (Tokens.RBRACK(yypos,yypos+1));
<INITIAL>")"               => (Tokens.RPAREN(yypos,yypos+1));
<INITIAL>";"               => (Tokens.SEMICOLON(yypos,yypos+1));
<INITIAL>"*"               => (Tokens.TIMES(yypos,yypos+1));


<INITIAL>"\""				=>	(	YYBEGIN STRINGFOUND; 
									last_open_string_pos := yypos; 
									inside_string := true; raw_string :=  ""; 
									continue()
								);
<INITIAL,COMMENTFOUND>"/*"	=> 	(	YYBEGIN COMMENTFOUND; 
									last_open_comment_pos := yypos;  
									comment_nesting_level := !comment_nesting_level + 1; 
									continue()
								);
<INITIAL>"*/"				=> 	(	ErrorMsg.error yypos ("Error: unmatched close comment detected "); 
									raise LexFailure; 
									continue()
								);


<STRINGFOUND>"\\\^"[@-_]	=> (raw_string := !raw_string ^ valOf(String.fromString(yytext)); continue());
<STRINGFOUND>\\				=> (YYBEGIN ESCAPEFOUND; continue());
<STRINGFOUND>\"				=> 	(	YYBEGIN INITIAL; 
									inside_string := false; 
									Tokens.STRING(!raw_string,!last_open_string_pos,yypos+4)
								);
<STRINGFOUND>[\ -~]			=> (raw_string := !raw_string ^ yytext; continue());
<STRINGFOUND>\n				=> (ErrorMsg.error yypos ("illegal newline in string "); raise LexFailure; continue());



<ESCAPEFOUND>[0-9]{3}		=>	(	raw_string := !raw_string ^ check_digits_escape(yytext, yypos, yypos+4); 
									YYBEGIN STRINGFOUND; 
									continue()
								);
<ESCAPEFOUND>"n"			=> (raw_string := !raw_string ^ "\n"; YYBEGIN STRINGFOUND; continue());
<ESCAPEFOUND>"t"			=> (raw_string := !raw_string ^ "\t"; YYBEGIN STRINGFOUND; continue());
<ESCAPEFOUND>"\""			=> (raw_string := !raw_string ^ "\""; YYBEGIN STRINGFOUND; continue());
<ESCAPEFOUND>"\\"			=> (raw_string := !raw_string ^ "\\"; YYBEGIN STRINGFOUND; continue());
<ESCAPEFOUND>{format_char}	=> (YYBEGIN FORMAT; continue());

<FORMAT>{format_char}  		=> (continue());
<FORMAT>"\\"				=> (YYBEGIN STRINGFOUND; continue());
<FORMAT>.					=> (ErrorMsg.error yypos ("illegal char after escape char"); raise LexFailure; continue());


<COMMENTFOUND>"*/"			=> 	(	comment_nesting_level := !comment_nesting_level - 1; 
									if !comment_nesting_level = 0 then 
										YYBEGIN INITIAL 
									else 
										(); 
									continue()
								);
<COMMENTFOUND>.				=> (continue());

\n						=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>[0-9]+			=> (Tokens.INT(valOf (Int.fromString yytext), yypos, yypos+size(yytext)));
[\ \t\r]+				=> (continue());
.						=> (ErrorMsg.error yypos ("illegal character " ^ yytext); raise LexFailure; continue());

