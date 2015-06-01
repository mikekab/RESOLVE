lexer grammar ResolveLexer;

ALL
    :   'all'
    ;

ALTERS
    :   'alt'
    |   'alters'
    ;

AND
    :   'and'
    ;

ARRAY
    :   'Array'
    ;

AXIOM
    :   'Axiom'
    ;

BASECASE
    :   'Base_Case'
    ;

BY
    :   'by'
    ;

CARTPROD
    :   'Cart_Prod'
    ;

CASE
    :   'Case'
    ;

CATEGORICAL
    :   'Categorical'
    ;

CHANGING
    :   'changing'
    ;

CLEARS
    :   'clr'
    |   'clears'
    ;

CONCEPT
    :   'Concept'
    ;

CONFIRM
    :   'Confirm'
    ;

CONSTRAINT
    :   'Constraint'
    |   'Constraints'
    |   'constraint'
    |   'constraints'
    ;

CONVENTION
    :   'Convention'
    |   'Conventions'
    |   'convention'
    |   'conventions'
    ;

COROLLARY
    :   'Corollary'
    ;

CORR
    :   'correspondence'
    ;

DECREASING
    :   'decreasing'
    ;

DEFINES
    :   'Defines'
    ;

DEFINITION
    :   'Definition'
    |   'Def'
    ;

DO
    :   'do'
    ;

DURATION
    :   'duration'
    ;

ELAPSED_TIME
    :   'elapsed_time'
    ;

ELSE
    :   'else'
    ;

END
    :   'end'
    ;

ENHANCED
    :   'enhanced'
    ;

ENHANCEMENT
    :   'Enhancement'
    ;

ENSURES
    :   'ensures'
    ;

EVALUATES
    :   'eval'
    |   'evaluates'
    ;

EXEMPLAR
    :   'exemplar'
    ;

EXISTS
    :   'exists'
    ;

EXTERNALLY
    :   'externally'
    ;

FACILITY
    :   'Facility'
    ;

FAC_FINAL
    :   'Facility_Finalization'
    ;

FAC_INIT
    :   'Facility_Initialization'
    ;

FAMILY
    :   'Family'
    ;

FINALIZATION
    :   'finalization'
    ;

FROM
    :   'from'
    ;

FOR
    :   'For'
    |   'for'
    ;

IF
    :   'if'
    ;

IMPLICIT
    :   'Implicit'
    ;

IMPLIES
    :   'implies'
    ;

IN
    :   'is_in'
    ;

INDUCTIVE
    :   'Inductive'
    ;

INDUCTIVE_BASE_NUM
    :   '(i.)'
    ;

INDUCTIVE_HYP_NUM
    :   '(ii.)'
    ;

INITIALIZATION
    :   'initialization'
    ;

INSTANTIATION
    :   'instantiation'
    ;

INTERSECT
    :   'intersect'
    ;

INTRODUCES
    :   'introduces'
    ;

IS
    :   'is'
    ;

ITERATE
    :   'Iterate'
    ;

LAMBDA
    :   'lambda'
    ;

LEMMA
    :   'Lemma'
    ;

MAINP_DISP
    :   'mainp_disp'
    ;

MAINTAINING
    :   'maintaining'
    ;

MOD
    :   'mod'
    ;

MODELED
    :   'modeled'
    ;

MODUS
    :   'modus'
    ;

NOT
    :   'not'
    ;

NOT_IN
    :   'is_not_in'
    ;

NOT_PROP_SUBSET
    :   'is_not_proper_subset_of'
    ;

NOT_SUBSET
    :   'is_not_subset_of'
    ;

NOT_SUBSTR
    :   'is_not_substring_of'
    ;

OF
    :   'of'
    ;

ON
    :   'on'
    ;

OP
    :   'op'
    ;

OPERATION
    :   'Oper'
    |   'Operation'
    ;

OR
    :   'or'
    ;

OTHERWISE
    :   'otherwise'
    ;

PERF_FINAL
    :   'perf_finalization'
    ;

PERF_INIT
    :   'perf_initialization'
    ;

PONENS
    :   'ponens'
    ;

PRECIS
    :   'Precis'
    ;

PRESERVES
    :   'pres'
    |   'preserves'
    ;

PROFILE
    :   'Profile'
    ;

PROCEDURE
    :   'Proc'
    |   'Procedure'
    ;

PROP_SUBSET
    :   'is_proper_subset_of'
    ;

REALIZATION
    :   'Realization'
    ;

REALIZED
    :   'realized'
    ;

RECORD
    :   'Record'
    ;

RECURSIVE
    :   'Recursive'
    ;

RELATED
    :   'related'
    ;

REMEMBER
    :   'Remember'
    ;

REPLACES
    :   'rpl'
    |   'replaces'
    ;

REPRESENTED
    :   'represented'
    ;

REQUIRES
    :   'requires'
    ;

RESTORES
    :   'rest'
    |   'restores'
    ;

SUBSET
    :   'is_subset_of'
    ;

SUBSTR
    :   'is_substring_of'
    ;

SUCH
    :   'such'
    ;

THAT
    :   'that'
    ;

THEN
    :   'then'
    ;

THEOREM
    :   'Theorem'
    ;

THERE
    :   'There'
    |   'there'
    ;

TYPE
    :   'Type'
    |   'type'
    ;

UNION
    :   'union'
    ;

UPDATES
    :   'upd'
    |   'updates'
    ;

USES
    :   'uses'
    ;

VAR
    :   'Var'
    ;

WHERE
    :   'where'
    ;

WHILE
    :   'While'
    ;

WITH_PROFILE
    :   'with_profile'
    ;

// Additional Symbol Tokens

ASSIGN_OP
    :   ':='
    ;

BAR
    :   '|'
    ;

COLON
    :   ':'
    ;

COMMA
    :   ','
    ;

CONCAT
    :   'o'
    ;

DBL_BAR
    :   '||'
    ;

DIVIDE
    :   '/'
    ;

DOT
    :   '.'
    ;

EQL
    :   '='
    ;

FUNCARROW
    :   '->'
    ;

GT
    :   '>'
    ;

GT_EQL
    :   '>='
    ;

HASH
    :   '#'
    ;

LBRACE
    :   '{'
    ;

LPAREN
    :   '('
    ;

LT
    :   '<'
    ;

LT_EQL
    :   '<='
    ;

MINUS
    :   '-'
    ;

MULTIPLY
    :   '*'
    ;

NOT_EQL
    :   '/='
    ;

PLUS
    :   '+'
    ;

QUALIFIER
    :   '::'
    ;

RANGE
    :   '..'
    ;

RBRACE
    :   '}'
    ;

RPAREN
    :   ')'
    ;

SEMICOLON
    :   ';'
    ;

SWAP_OP
    :   ':=:'
    ;

TILDE
    :   '~'
    ;

// literal rules and fragments

BOOLEAN_LITERAL
    :   'B'
    |   'false'
    |   'true'
    ;

INTEGER_LITERAL
    :   DecimalIntegerLiteral
    ;

CHARACTER_LITERAL
    :   '\'' SingleCharacter '\''
    ;

STRING_LITERAL
    :   '\"' StringCharacters? '\"'
    ;

fragment
StringCharacters
    :   StringCharacter+
    ;

fragment
StringCharacter
    :   ~["\\]
    ;

fragment
DecimalIntegerLiteral
    :   '0'
    |   NonZeroDigit (Digits)?
    ;

fragment
Digits
    :   Digit (Digit)*
    ;

fragment
Digit
    :   '0'
    |   NonZeroDigit
    ;

fragment
NonZeroDigit
    :   [1-9]
    ;

fragment
SingleCharacter
    :   ~['\\]
    ;

// whitespace, identifier rules, and comments

COMMENT
    :   '(*' .*? '*)' -> skip
    ;

IDENTIFIER
    :   LETTER LETTER_OR_DIGIT*
    ;

LETTER
    :   [a-zA-Z$_]
    ;

LETTER_OR_DIGIT
    :   [a-zA-Z0-9$_]
    ;

LINE_COMMENT
    :   '--' ~[\r\n]* -> skip
    ;

SPACE
    :  [ \t\r\n\u000C]+ -> skip
    ;