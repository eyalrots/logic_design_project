module ShiftRows #(
    parameter int N    = 128,
    parameter int BYTE = 8,
    parameter int WORD = 32
)(
    input  logic [N-1:0] Text_In_T,
    output logic [N-1:0] Out_Text_T
);

    // =========================================================================
    // AES ShiftRows (Reversed Row Logic - Explicit Byte Shifts)
    // =========================================================================
    // The logic below constructs the output words by explicitly selecting
    // the source bytes based on the shift amount.
    //
    // Notation: 
    // In[3], In[2], In[1], In[0] refers to the 4 bytes of the input row.
    // Concatenation is {MSB, ..., LSB}, so {In[2], In[1], In[0], In[3]}
    // creates the byte sequence 2, 1, 0, 3 in the output word.

    // -------------------------------------------------------------------------
    // Row 0: Shift Left 1 (Sequence: 0,1,2,3 -> 1,2,3,0)
    // -------------------------------------------------------------------------
    // Output Order (LSB first): Byte 1, Byte 2, Byte 3, Byte 0
    // Concatenation (MSB first): { Byte 0, Byte 3, Byte 2, Byte 1 }
    assign Out_Text_T[WORD-1 : 0] = {
        Text_In_T[0        +: BYTE],       // Byte 0
        Text_In_T[(3*BYTE) +: BYTE],       // Byte 3
        Text_In_T[(2*BYTE) +: BYTE],       // Byte 2
        Text_In_T[(BYTE)   +: BYTE]        // Byte 1
    };

    // -------------------------------------------------------------------------
    // Row 1: Shift Left 2 (Sequence: 0,1,2,3 -> 2,3,0,1)
    // -------------------------------------------------------------------------
    // Output Order (LSB first): Byte 2, Byte 3, Byte 0, Byte 1
    // Concatenation (MSB first): { Byte 1, Byte 0, Byte 3, Byte 2 }
    assign Out_Text_T[2*WORD-1 : WORD] = {
        Text_In_T[(WORD + BYTE)   +: BYTE], // Byte 1 (of Row 1)
        Text_In_T[(WORD)          +: BYTE], // Byte 0 (of Row 1)
        Text_In_T[(WORD + 3*BYTE) +: BYTE], // Byte 3 (of Row 1)
        Text_In_T[(WORD + 2*BYTE) +: BYTE]  // Byte 2 (of Row 1)
    };

    // -------------------------------------------------------------------------
    // Row 2: Shift Left 3 (Sequence: 0,1,2,3 -> 3,0,1,2)
    // -------------------------------------------------------------------------
    // Output Order (LSB first): Byte 3, Byte 0, Byte 1, Byte 2
    // Concatenation (MSB first): { Byte 2, Byte 1, Byte 0, Byte 3 }
    assign Out_Text_T[3*WORD-1 : 2*WORD] = {
        Text_In_T[(2*WORD + 2*BYTE) +: BYTE], // Byte 2 (of Row 2)
        Text_In_T[(2*WORD + BYTE)   +: BYTE], // Byte 1 (of Row 2)
        Text_In_T[(2*WORD)          +: BYTE], // Byte 0 (of Row 2)
        Text_In_T[(2*WORD + 3*BYTE) +: BYTE]  // Byte 3 (of Row 2)
    };

    // -------------------------------------------------------------------------
    // Row 3: No Shift (Sequence: 0,1,2,3 -> 0,1,2,3)
    // -------------------------------------------------------------------------
    assign Out_Text_T[4*WORD-1 : 3*WORD] = Text_In_T[4*WORD-1 : 3*WORD];

endmodule