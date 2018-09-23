#lang racket

(provide four-queens)
;;There are 16 variables, each denoting whether there is a queen in that square

(define four-queens
  '((x11 x12 x13 x14)(x21 x22 x23 x24)(x31 x32 x33 x34)(x41 x42 x43 x44)       ;;Atleast one queen in each row
    ;First row constraint
    (-x11 -x12) (-x11 -x13) (-x11 -x14)
    (-x12 -x11) (-x12 -x13) (-x12 -x14)
    (-x13 -x11) (-x13 -x12) (-x13 -x14)
    (-x14 -x11) (-x14 -x12) (-x14 -x13)
    ;Second row constraint
    (-x21 -x22) (-x21 -x23) (-x21 -x24)
    (-x22 -x21) (-x22 -x23) (-x22 -x24)
    (-x23 -x21) (-x23 -x22) (-x23 -x24)
    (-x24 -x21) (-x24 -x22) (-x24 -x23)
    ;Third row constraint
    (-x31 -x32) (-x31 -x33) (-x31 -x34)
    (-x32 -x31) (-x32 -x33) (-x32 -x34)
    (-x33 -x31) (-x33 -x32) (-x33 -x34)
    (-x34 -x31) (-x34 -x32) (-x34 -x33)
    ;Fourth row constraint
    (-x41 -x42) (-x41 -x43) (-x41 -x44)
    (-x42 -x41) (-x42 -x43) (-x42 -x44)
    (-x43 -x41) (-x43 -x42) (-x43 -x44)
    (-x44 -x41) (-x44 -x42) (-x44 -x43)
    ;First Column constraint
    (-x11 -x21) (-x11 -x31) (-x11 -x41)
    (-x21 -x11) (-x21 -x31) (-x21 -x41)
    (-x31 -x11) (-x31 -x21) (-x31 -x41)
    (-x41 -x11) (-x41 -x21) (-x41 -x31)
    ;Second Column constraint
    (-x12 -x22) (-x12 -x32) (-x12 -x42)
    (-x22 -x12) (-x22 -x32) (-x22 -x42)
    (-x32 -x12) (-x32 -x22) (-x32 -x42)
    (-x42 -x12) (-x42 -x22) (-x42 -x32)
    ;Second Column constraint
    (-x13 -x23) (-x13 -x33) (-x13 -x43)
    (-x23 -x13) (-x23 -x33) (-x23 -x43)
    (-x33 -x13) (-x33 -x23) (-x33 -x43)
    (-x43 -x13) (-x43 -x23) (-x43 -x33)
    ;Second Column constraint
    (-x14 -x24) (-x14 -x34) (-x14 -x44)
    (-x24 -x14) (-x24 -x34) (-x24 -x44)
    (-x34 -x14) (-x34 -x24) (-x34 -x44)
    (-x44 -x14) (-x44 -x24) (-x44 -x34)

    ;The Diagonal Constraints
    (-x11 -x22) (-x11 -x33) (-x11 -x33)
    (-x12 -x21) (-x12 -x23) (-x12 -x34)
    (-x21 -x12) (-x21 -x32) (-x21 -x43)
    (-x13 -x24) (-x13 -x22) (-x13 -x31)
    (-x22 -x11) (-x22 -x33) (-x22 -x44) (-x22 -x13) (-x22 -x31)
    (-x31 -x42) (-x31 -x22) (-x31 -x13)
    (-x14 -x23) (-x14 -x32) (-x14 -x41)
    (-x23 -x12) (-x23 -x34) (-x23 -x14) (-x23 -x32) (-x23 -x41)
    (-x32 -x21) (-x32 -x43) (-x32 -x41) (-x32 -x23) (-x32 -x14)
    (-x41 -x32) (-x41 -x23) (-x41 -x14)
    (-x24 -x13) (-x24 -x33) (-x24 -x42)
    (-x33 -x44) (-x33 -x22) (-x33 -x11) (-x33 -x42) (-x33 -x24)
    (-x42 -x31) (-x42 -x33) (-x42 -x24)
    (-x34 -x43)))  ;;Taking a short cut here...This could have saved lots of clauses... Improve in future.
    
    