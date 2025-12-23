# MIX COLUMNS PROJECT

## Mix_operation.sv  
    this module has the core calculation of the Mix columns part.
    that is, the miltiplication of elements the matrices, i.e. 01/02/03 * 0xXX,
    by the formula: 01 = 1 ; 02 = x ; 03 = x + 1 ; 08 = x^4 + x^3 + x + 1.

## Mix_columns.sv    
    this module is resposible for the overall operation of the mix coplums.
    that is the multiplication of the two two matrices, ont from the sub_bytes operation
    and one of the coefficients.

## sbox.sv           
    this module was given to us. it is responsible for the mapping of vectors.

## sub_bytes.sv
    this module as well was given to us. it is responsible for the sub bytes operation.

## shift_rows.sv
    This module performs the operation of shift for a matrix's rows.
    First row shifts by 0, second by 1, third by 2, forth by 3. 
    (The shift is left arithmetically).

## fsm.sv
    This module is the TOP module of the system.
    It operates the FSM (finite state machine) by which the system works.
    It has registered output for signal stability.
    States of the FSM transfer synchronizly, that is each state goes to the next, the last to reset:
    RESET -> CASE_2 -> CASE_3 -> RESET -> ...
    RESET  - both out signals return to 0.
    CASE_2 - onlt a sub bytes operation that goes to the output signal sb_out.
    CASE_3 - a sub bytes operation followed by a mix columns operation that then goes the the output signal mix_out.

## Mix_columns_tb.sv 
    This is the test file. It inserts a vector as input to the fsm and receives an output of sub bytes and mix columns.
    Clock operates at 10ps per cycle (100 GHz).
    RESET = 1 for one clock cycle then 0.