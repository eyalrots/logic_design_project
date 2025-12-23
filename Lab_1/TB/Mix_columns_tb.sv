`timescale 1ns / 1ps
module fsm_tb;
    localparam DIM = 4;
    localparam WIDTH = 8;

    // type definitions:
    typedef logic [WIDTH-1:0] matrix_t [DIM-1:0][DIM-1:0];

    logic clk, rst;
    logic [WIDTH*DIM*DIM-1:0] vec_i_tb;   // from Plaintext
    matrix_t mix_out_tb, sb_out_tb;

    // clk generation
    initial clk = 0;
    always #5 clk = ~clk;

    //rst generation
    initial begin
        rst = 1;
        #10;
        rst = 0;
    end

    initial begin
        vec_i_tb = 128'h19a09ae93df4c6f8e3e28d48be2b2a08;
        #500
        $display("Input:  %p", vec_i_tb);
        $display("Output: %p", mix_out_tb);
        $display("Output: %p", sb_out_tb);
        
        // Stop the simulation
        //$finish;

    end

    fsm FSM_m ( 
        .clk_i(clk),
        .rst_i(rst),  
        .vec_i(vec_i_tb),
        .mix_out(mix_out_tb),
        .sb_out(sb_out_tb)
    );

endmodule