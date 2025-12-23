module fsm #(
    parameter WIDTH = 8,
    parameter DIM   = 4
) (
    input clk_i, rst_i,
    input [DIM*DIM*WIDTH-1:0] vec_i,
    output wire [WIDTH-1:0] sb_out [DIM-1:0][DIM-1:0],
    output wire [WIDTH-1:0] mix_out [DIM-1:0][DIM-1:0]
);

    // type definitions:
    typedef reg [WIDTH-1:0] matrix_t [DIM-1:0][DIM-1:0];

    // parameters and variables:
    parameter [1:0] RESET  = 2'b00,
                    CASE_1 = 2'b01,
                    CASE_2 = 2'b10,
                    CASE_3 = 2'b11;

    reg [1:0] state, next;

    matrix_t sb_mat_1, sb_mat_2, mix_mat;

    reg [WIDTH*DIM*DIM-1:0] sb_vec_1, sb_vec_2, shifted_1, shifted_2;

    // functions and module calls:
    function automatic matrix_t vec2mat (input reg [WIDTH*DIM*DIM-1:0] vec);
        matrix_t mat_r;
        int bit_idx = 0;
        
        for (int i = 0; i < DIM; i++) begin
            for (int j = 0; j < DIM; j++) begin
                mat_r[i][j] = vec[bit_idx +: WIDTH];
                bit_idx = bit_idx + WIDTH;
            end
        end
        
        return mat_r;
    endfunction


    subBytes sub_byte_1 (
        .in(vec_i),
        .out(sb_vec_1)
    );
    ShiftRows shift_1 (
        .Text_In_T(sb_vec_1),
        .Out_Text_T(shifted_1)
    );

    subBytes sub_byte_2 (
        .in(vec_i),
        .out(sb_vec_2)
    );
    ShiftRows shift_2 (
        .Text_In_T(sb_vec_2),
        .Out_Text_T(shifted_2)
    );

    Mix_columns #(
        .DIM(DIM), .WIDTH(WIDTH)
    ) mix_cols (
        .mat_i(sb_mat_2),
        .mat_o(mix_mat)
    );

    // state update for FSM on clk / rst:
    always_ff @(posedge clk_i, negedge rst_i) begin
        if (rst_i)
            state <= RESET;
        else
            state <= next;
    end

    // next state combinational update:
    always @(state) begin
        case (state)
        RESET: begin
            next = CASE_2;
        end
        CASE_2: begin
            next = CASE_3;
        end
        CASE_3: begin
            next = RESET;
        end
        default: begin
            next = RESET;
        end
        endcase
    end

    // output registers
    // --- registered output ---
    always_ff @(posedge clk_i) begin
        case (state)
        RESET: begin
            sb_mat_1 <= vec2mat('0);
            sb_mat_2 <= vec2mat('0);
        end
        CASE_2: begin
            sb_mat_1 <= vec2mat(shifted_1);
        end
        CASE_3: begin
            sb_mat_2 <= vec2mat(shifted_2);
        end
        default: begin
            sb_mat_1 <= vec2mat('0);
            sb_mat_2 <= vec2mat('0);
        end
        endcase
    end

    // case 2 output:
    assign sb_out  = sb_mat_1;
    // case 3 output:
    assign mix_out = mix_mat;
        
endmodule