package maf.core

/** Type of an expression. Can be used to distinguish expressions based on their type. */
enum Label:
    // Identifiers
    case SYM // Identifier

    // Scheme
    case BEG // Begin
    case DFV // Variable definition
    case FNC // Function call (application)
    case IFF // If expression
    case LAM // Lambda expression
    case LET // Let expression
    case LTR // Letrec expression
    case LTS // Let* expression
    case PAI // Pair expression
    case VEC // Vector expression
    case SET // Assignment
    case VAL // Value
    case VAR // Variable

    // Assertions
    case ASS // Assertion

    // Code changes
    case CHA // Code change

    // Concurrent Scheme
    case FRK // Fork
    case JOI // Join

    // Actor Scheme
    case ACT // Actor behavior expression
    case SEL // Actor select a message
    case SEN // Actor send expression
    case BEC // Actor become expression
    case CREA // Actor create expression
    case ASK // Actor ask expression
    case AWAIT // Actor await expression

    // Contract language
    case DFC // define/contract
    case DPC // Dependent contract
    case FLC // Flat contract
    case MON // Monitor
    case CHK // Check expression

    // Contract language for actors
    case MCC // message/c contract
    case ENS // ensure/c contract

    // Racket module system (used in the contract language)
    case PROV // Provide expression
    case PCO // Provide contract-out element

    // Structs
    case MSG // Struct getter
    case MSS // Struct setter
    case MSC // Struct constructor
    case MSP // Struct predicate

    // Match expressions
    case MEX // match expression

    // Symbolic language
    case HOL // a symbolic hole
    case SVR // a symbolic variable

    // Taint analysis
    case SRC // Source
    case SNK // Sink
    case SAN // Sanitiser
