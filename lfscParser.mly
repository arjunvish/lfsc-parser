%{
(* This translator is adapted from SMTCoq's LFSC translator *)

open Lexing
open Format

let concat_sp_sep_2 a b = "("^a^" "^b^")"
let concat_sp_sep_3 a b c = "("^a^" "^b^" "^c^")"
let concat_sp_sep_4 a b c d = "("^a^" "^b^" "^c^" "^d^")"
let concat_sp_sep_5 a b c d e = "("^a^" "^b^" "^c^" "^d^" "^e^")"
let concat_sp_sep_6 a b c d e f = "("^a^" "^b^" "^c^" "^d^" "^e^" "^f^")"
let concat_sp_sep_7 a b c d e f g = "("^a^" "^b^" "^c^" "^d^" "^e^" "^f^" "^g^")"
let concat_sp_sep_8 a b c d e f g h = "("^a^" "^b^" "^c^" "^d^" "^e^" "^f^" "^g^" "^h^")"
%}

%token <string> IDENT
%token <string> ANYTHING
%token <int> INT
%token LPAREN RPAREN EOF HASH_SEMI
%token LAMBDA PI BIGLAMBDA COLON
%token CHECK
%token MPQ MPZ HOLE TYPE KIND
%token SC PROGRAM AT
%token VAR HOLDS
%token CLC CLN POS NEG
%token SATLEM_SIMPLIFY SATLEM RRES QRES
%token CONCAT_CL CLR
%token CNFN CNFC CNF_HOLDS CNFN_PROOF CNFC_PROOF
%token TH_HOLDS TRUE FALSE NOT AND OR IMPL
%token IFF XOR IFTE TERM EQUALS ITE LET FLET
%token BOOL P_APP T_TRUE T_FALSE T_T_NEQ_F
%token PRED_EQ_T PRED_EQ_F F_TO_B
%token TRUE_PREDS_EQUAL FALSE_PREDS_EQUAL
%token PRED_REFL_POS PRED_REFL_NEG
%token PRED_NOT_IFF_F PRED_NOT_IFF_F_2
%token PRED_NOT_IFF_T PRED_NOT_IFF_T_2
%token PRED_IFF_F PRED_IFF_F_2
%token PRED_IFF_T PRED_IFF_T_2
%token DECL_ATOM DECL_BVATOM
%token CLAUSIFY_FORM CLAUSIFY_FORM_NOT
%token CLAUSIFY_FALSE TH_LET_PF
%token IFF_SYMM CONTRAD TRUTH NOT_NOT_INTRO
%token NOT_NOT_ELIM OR_ELIM_1 OR_ELIM_2
%token NOT_OR_ELIM AND_ELIM_1 AND_ELIM_2
%token NOT_AND_ELIM IMPL_INTRO IMPL_ELIM
%token NOT_IMPL_ELIM IFF_ELIM_1 IFF_ELIM_2
%token NOT_IFF_ELIM XOR_ELIM_1 XOR_ELIM_2
%token NOT_XOR_ELIM  ITE_ELIM_1 ITE_ELIM_2
%token ITE_ELIM_3 NOT_ITE_ELIM_1 NOT_ITE_ELIM_2
%token NOT_ITE_ELIM_3 AST ASF BV_AST BV_ASF
%token TRUST TRUST_F ARROW APPLY REFL SYMM
%token TRANS NEGSYMM NEGTRANS1 NEGTRANS2 CONG
%token SORT

%start command
%type <unit> command
%%

lit:
  | LPAREN POS IDENT RPAREN
    { concat_sp_sep_2 "lit.pos" ($3) }
  | LPAREN NEG IDENT RPAREN
    { concat_sp_sep_2 "lit.neg" ($3) }
;

clause:
  | CLN { "[]" }
  | LPAREN CLC lit clause RPAREN
    { ($3^" :: "^$4) }
  | LPAREN CONCAT_CL clause clause RPAREN
    { ("concat_cl "^$3^" "^$4) }
  | LPAREN CLR lit clause RPAREN
    { ("clr "^$3^" "^$4) }
  | HOLE { "" }
;

cnf:
  | CNFN { "[]" }
  | LPAREN CNFC clause cnf RPAREN
    { ("("^$3^") :: ("^$4^")") }
  | HOLE { "" }
;

arrow_sort:
  | BOOL { "Bool" }
  | LPAREN ARROW arrow_sort arrow_sort RPAREN
    { ("("^$3^")"^" "^$4^")") }
;

sort:
  | LPAREN ARROW arrow_sort arrow_sort RPAREN 
    { ("("^$3^")"^" "^$4^")") }
  | IDENT { "IFUCKEDUP!-sort->IDENT" }
  | HOLE { "IFUCKEDUP!-sort->HOLE" }
;

sorted_term:
  | LPAREN ITE sort formula sorted_term sorted_term RPAREN
    { concat_sp_sep_5 "ite" $3 $4 $5 $6 }
  | T_TRUE { "true" }
  | T_FALSE { "false" }
  | LPAREN F_TO_B formula RPAREN
    { $3 }
  | LPAREN APPLY sort sort sorted_term sorted_term RPAREN
    { concat_sp_sep_2 $5 $6 }
  | IDENT { ($1) }
  | HOLE { "" }
;

formula:
  | TRUE { "true" }
  | FALSE { "false" }
  | LPAREN NOT formula RPAREN 
    { (concat_sp_sep_2 "not" $3) }
  | LPAREN AND formula formula RPAREN
    { (concat_sp_sep_3 "and" $3 $4) }
  | LPAREN OR formula formula RPAREN
    { (concat_sp_sep_3 "or" $3 $4) }
  | LPAREN IMPL formula formula RPAREN
    { (concat_sp_sep_3 "=>" $3 $4) }
  | LPAREN IFF formula formula RPAREN
    { (concat_sp_sep_3 "=" $3 $4) }
  | LPAREN XOR formula formula RPAREN
    { (concat_sp_sep_3 "xor" $3 $4) }
  | LPAREN IFTE formula formula formula RPAREN
    { (concat_sp_sep_4 "ite" $3 $4 $5) }
  | LPAREN EQUALS sort sorted_term sorted_term RPAREN
    { "IFUCKEDUP!" }
  | LET sort sorted_term LPAREN LAMBDA IDENT formula RPAREN
    { "IFUCKEDUP!" }
  | FLET formula LPAREN LAMBDA IDENT formula RPAREN
    { "IFUCKEDUP!" }
  | LPAREN P_APP sorted_term RPAREN { $3 }
  | HOLE { "" }
;

holds_term:
  | LPAREN HOLDS clause RPAREN
    { ("holds ("^$3^")") }
  | LPAREN CNF_HOLDS cnf RPAREN
    { ("cnf_holds ("^$3^")") }
  | LPAREN TH_HOLDS formula RPAREN
    { ($3) }
  | IDENT { $1 }
;

proof_term:
  | LPAREN SATLEM clause clause proof_term proof_term RPAREN
    { "(satlem "^$3^$4^$5^" "^$6^")" }
  | LPAREN SATLEM_SIMPLIFY clause clause clause proof_term proof_term RPAREN
    { "(satlem_simplify "^$3^$4^$5^$6^" \n"^" _ "^$7^")" }
  | LPAREN RRES clause clause proof_term proof_term IDENT RPAREN
    { "(R "^$3^$4^$5^" "^$6^" "^$7^")" }
  | LPAREN QRES clause clause proof_term proof_term IDENT RPAREN
    { "(Q "^$3^$4^$5^" "^$6^" "^$7^")" }
  | LPAREN LAMBDA IDENT proof_term RPAREN { "(fun "^$3^",\n   "^$4^")" }
  | CNFN_PROOF { "cnfn_proof" }
  | LPAREN CNFC_PROOF clause clause cnf proof_term proof_term RPAREN
    { "(cnfc_proof \n"^$3^$4^$5^" "^$6^" "^$7^")" }
  | T_T_NEQ_F { "t_t_neq_f" }
  | LPAREN PRED_EQ_T sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_eq_t" $3 $4 }
  | LPAREN PRED_EQ_F sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_eq_f" $3 $4 }
  | LPAREN TRUE_PREDS_EQUAL sorted_term sorted_term holds_term holds_term RPAREN
    { concat_sp_sep_5 "true_preds_equal" $3 $4 $5 $6 }
  | LPAREN FALSE_PREDS_EQUAL sorted_term sorted_term holds_term holds_term RPAREN
    { concat_sp_sep_5 "false_preds_equal" $3 $4 $5 $6 }
  | LPAREN PRED_REFL_POS sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_refl_pos" $3 $4 }
  | LPAREN PRED_REFL_NEG sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_refl_neg" $3 $4 }
  | LPAREN PRED_NOT_IFF_F sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_f" $3 $4 }
  | LPAREN PRED_NOT_IFF_F_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_f_2" $3 $4 }
  | LPAREN PRED_NOT_IFF_T sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_t" $3 $4 }
  | LPAREN PRED_NOT_IFF_T_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_not_iff_t_2" $3 $4 }
  | LPAREN PRED_IFF_F sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_f" $3 $4 }
  | LPAREN PRED_IFF_F_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_f_2" $3 $4 }
  | LPAREN PRED_IFF_T sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_t" $3 $4 }
  | LPAREN PRED_IFF_T_2 sorted_term holds_term RPAREN
    { concat_sp_sep_3 "pred_iff_t_2" $3 $4 }
  | LPAREN DECL_ATOM formula proof_term RPAREN
    { concat_sp_sep_3 "decl_atom" $3 $4 }
  | LPAREN DECL_BVATOM formula proof_term RPAREN
    { concat_sp_sep_3 "decl_bv_atom" $3 $4 }
  | LPAREN CLAUSIFY_FORM formula proof_term proof_term proof_term RPAREN
    { concat_sp_sep_5 "clausify_form" $3 $4 $5 $6 }
  | LPAREN CLAUSIFY_FORM_NOT formula proof_term proof_term proof_term RPAREN
    { concat_sp_sep_5 "clausify_form_not" $3 $4 $5 $6 }
  | LPAREN CLAUSIFY_FALSE proof_term RPAREN
    { concat_sp_sep_2 "clausify_false" $3 }
  | LPAREN TH_LET_PF formula proof_term proof_term RPAREN
    { concat_sp_sep_4 "th_let_pf" $3 $4 $5 }
  | LPAREN IFF_SYMM formula RPAREN
    { concat_sp_sep_2 "iff_symm" $3 }
  | LPAREN CONTRAD formula proof_term proof_term RPAREN
    { concat_sp_sep_4 "contra" $3 $4 $5 }
  | TRUTH { "truth" }
  | LPAREN NOT_NOT_INTRO formula proof_term RPAREN
    { concat_sp_sep_3 "not_not_intro" $3 $4 }
  | LPAREN NOT_NOT_ELIM formula proof_term RPAREN
    { concat_sp_sep_3 "not_not_elim" $3 $4 }
  | LPAREN OR_ELIM_1 formula formula proof_term proof_term RPAREN
    { concat_sp_sep_3 "or_elim_1" $5 $6 }
  | LPAREN OR_ELIM_2 formula formula proof_term proof_term RPAREN
    { concat_sp_sep_3 "or_elim_2" $5 $6 }
  | LPAREN NOT_OR_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_or_elim" $5 }
  | LPAREN AND_ELIM_1 formula formula proof_term RPAREN
    { concat_sp_sep_2 "and_elim_1" $5 }
  | LPAREN AND_ELIM_2 formula formula proof_term RPAREN
    { concat_sp_sep_2 "and_elim_2" $5 }
  | LPAREN NOT_AND_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_and_elim" $5 }
  | LPAREN IMPL_INTRO formula formula proof_term RPAREN
    { concat_sp_sep_2 "impl_intro" $5 }
  | LPAREN IMPL_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "impl_elim" $5 }
  | LPAREN NOT_IMPL_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_impl_elim" $5 }
  | LPAREN IFF_ELIM_1 formula formula proof_term RPAREN
    { concat_sp_sep_2 "iff_elim_1" $5 }
  | LPAREN IFF_ELIM_2 formula formula proof_term RPAREN
    { concat_sp_sep_2 "iff_elim_2" $5 }
  | LPAREN NOT_IFF_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_iff_elim" $5 }
  | LPAREN XOR_ELIM_1 formula formula proof_term RPAREN
    { concat_sp_sep_2 "xor_elim_1" $5 }
  | LPAREN XOR_ELIM_2 formula formula proof_term RPAREN
    { concat_sp_sep_2 "xor_elim_2" $5 }
  | LPAREN NOT_XOR_ELIM formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_xor_elim" $5 }
  | LPAREN ITE_ELIM_1 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "ite_elim_1" $6 }
  | LPAREN ITE_ELIM_2 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "ite_elim_2" $6 }
  | LPAREN ITE_ELIM_3 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "ite_elim_3" $6 }
  | LPAREN NOT_ITE_ELIM_1 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_ite_elim_1" $6 }
  | LPAREN NOT_ITE_ELIM_2 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_ite_elim_2" $6 }
  | LPAREN NOT_ITE_ELIM_3 formula formula formula proof_term RPAREN
    { concat_sp_sep_2 "not_ite_elim_3" $6 }
  | LPAREN AST proof_term formula clause proof_term proof_term RPAREN
    { concat_sp_sep_6 "ast" $3 $4 $5 $6 $7 }
  | LPAREN ASF proof_term formula clause proof_term proof_term RPAREN
    { concat_sp_sep_6 "asf" $3 $4 $5 $6 $7 }
  | LPAREN BV_ASF proof_term proof_term formula clause proof_term proof_term proof_term RPAREN
    { concat_sp_sep_8 "bv_asf" $3 $4 $5 $6 $7 $8 $9 }
  | LPAREN BV_AST proof_term proof_term formula clause proof_term proof_term proof_term RPAREN
    { concat_sp_sep_8 "bv_ast" $3 $4 $5 $6 $7 $8 $9 }
  | TRUST { "trust" }
  | LPAREN TRUST_F formula RPAREN
    { concat_sp_sep_2 "trust_f" $3 }
  | LPAREN REFL sort sorted_term RPAREN
    { concat_sp_sep_2 "refl" $4 }
  | LPAREN SYMM sort sorted_term sorted_term proof_term RPAREN
    { concat_sp_sep_2 "symm" $6 }
  | LPAREN TRANS sort sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "trans" $7 $8 }
  | LPAREN NEGSYMM sort sorted_term sorted_term proof_term RPAREN
    { concat_sp_sep_2 "negsymm" $6 }
  | LPAREN NEGTRANS1 sort sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "negtrans1" $7 $8 }
  | LPAREN NEGTRANS2 sort sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "negtrans2" $7 $8 }
  | LPAREN CONG sort sort sorted_term sorted_term sorted_term sorted_term proof_term proof_term RPAREN
    { concat_sp_sep_3 "cong" $9 $10 }
  | HOLE { "" }
  | IDENT { (" "^$1^" ") }
;

typed_var:
  | IDENT VAR { "IFUCKEDUP!-typed_var->IDENT VAR" }
  | IDENT LPAREN TERM BOOL RPAREN
    { ("(declare-fun "^$1^" () Bool)") }
  | IDENT LPAREN TERM sort RPAREN 
    { ("(declare-fun "^$1^" "^$4^")") }
  | IDENT SORT { ($1^" : sort") }
  | IDENT holds_term 
    { ("(assert "^$2^")")}
;
/*
holds_anything_term:
  | LPAREN ANYTHING RPAREN
    { "" }
;

proof_anything_term:
  | LPAREN ANYTHING RPAREN
    { "" }
;
*/
term:
  | LPAREN COLON holds_term proof_term RPAREN
    { "" }
  | LPAREN BIGLAMBDA typed_var term RPAREN
    { $3^"\n"^$4 }
;

check_command:
  | LPAREN CHECK term RPAREN
    { print_string 
      ("(set-logic ALL_SUPPORTED)\n"
        ^$3^"(check-sat)\n") }
;

command:
  | check_command EOF { $1 }
;