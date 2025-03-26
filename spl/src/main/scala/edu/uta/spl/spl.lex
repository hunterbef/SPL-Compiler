/********************************************************************************
*
* File: spl.lex
* The SPL scanner
*
********************************************************************************/

package edu.uta.spl;

import java_cup.runtime.Symbol;

%%
%class SplLex
%public
%line
%column
%cup

DIGIT=0|[1-9][0-9]*
ID=[a-zA-Z][a-zA-Z0-9_]*

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]

Comment = {TraditionalComment} | {EndOfLineComment} | {DocumentationComment}
TraditionalComment   = "/*" [^*] ~"*/" | "/*" "*"+ "/"
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}?
DocumentationComment = "/**" {CommentContent} "*"+ "/"
CommentContent       = ( [^*] | \*+ [^/*] )*

%{

  private Symbol symbol ( int type )
  {
    return new Symbol(type, yyline+1, yycolumn+1);
  }

  private Symbol symbol ( int type, Object value )
  {
    return new Symbol(type, yyline+1, yycolumn+1, value);
  }

  public void lexical_error ( String message )
  {
    System.err.println("*** Lexical Error: " + message + " (line: " + (yyline+1)
                       + ", position: " + (yycolumn+1) + ")");
    System.exit(1);
  }
%}

%%
<YYINITIAL> "bool"          { return symbol(sym.BOOLEAN); }
<YYINITIAL> "array"         { return symbol(sym.ARRAY); }
<YYINITIAL> "by"            { return symbol(sym.BY); }
<YYINITIAL> "def"           { return symbol(sym.DEF); }
<YYINITIAL> "else"          { return symbol(sym.ELSE); }
<YYINITIAL> "exit"          { return symbol(sym.EXIT); }
<YYINITIAL> "false"         { return symbol(sym.FALSE); }
<YYINITIAL> "float"         { return symbol(sym.FLOAT); }
<YYINITIAL> "for"           { return symbol(sym.FOR); }
<YYINITIAL> "if"            { return symbol(sym.IF); }
<YYINITIAL> "int"           { return symbol(sym.INT); }
<YYINITIAL> "loop"          { return symbol(sym.LOOP); }
<YYINITIAL> "not"           { return symbol(sym.NOT); }
<YYINITIAL> "print"         { return symbol(sym.PRINT); }
<YYINITIAL> "read"          { return symbol(sym.READ); }
<YYINITIAL> "return"        { return symbol(sym.RETURN); }
<YYINITIAL> "String"        { return symbol(sym.STRING); }
<YYINITIAL> "to"            { return symbol(sym.TO); }
<YYINITIAL> "type"          { return symbol(sym.TYPE); }
<YYINITIAL> "var"           { return symbol(sym.VAR); }
<YYINITIAL> "while"         { return symbol(sym.WHILE); }
<YYINITIAL> "true"          { return symbol(sym.TRUE); }


<YYINITIAL>
{
    /*identifiers*/

    {ID}                    { return symbol(sym.ID, yytext()); }


    /*literals*/

    \"[^\"]*\"              { return symbol(sym.STRING_LITERAL, yytext().substring(1,yytext().length()-1)); }
    {DIGIT}+                { return symbol(sym.INTEGER_LITERAL, new Integer(yytext())); }
    {DIGIT}+"."{DIGIT}+     { return symbol(sym.FLOAT_LITERAL, new Float(yytext())); }


    /*operators*/

    "&&"                    { return symbol(sym.AND); }
    "/"                     { return symbol(sym.DIV); }
    "="                     { return symbol(sym.EQUAL); }
    "%"                     { return symbol(sym.MOD); }
    "+"                     { return symbol(sym.PLUS); }
    "||"                    { return symbol(sym.OR); }
    "-"                     { return symbol(sym.MINUS); }
    "*"                     { return symbol(sym.TIMES); }
    "<"                     { return symbol(sym.LT); }
    "<="                    { return symbol(sym.LEQ); }
    ">"                     { return symbol(sym.GT); }
    ">="                    { return symbol(sym.GEQ); }
    "=="                    { return symbol(sym.EQ); }
    "<>"                    { return symbol(sym.NEQ); }
    ":"                     { return symbol(sym.COLON); }
    ";"                     { return symbol(sym.SEMI); }
    ","                     { return symbol(sym.COMMA); }
    "#"                     { return symbol(sym.SHARP); }
    "."                     { return symbol(sym.DOT); }
    "("                     { return symbol(sym.LP); }
    ")"                     { return symbol(sym.RP); }
    "{"                     { return symbol(sym.LB); }
    "}"                     { return symbol(sym.RB); }
    "["                     { return symbol(sym.LSB); }
    "]"                     { return symbol(sym.RSB); }

    /*comments*/

    {Comment}               { /* ignore */ }


    /*whitespace*/

    [ \t\f\r\n]            { /* ignore white spaces. */ }
}

.                       { lexical_error("Illegal character"); }