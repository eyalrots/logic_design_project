`timescale  1ns/1ps

module tb_top;

localparam WIDTH = 8, DIM = 4;

typedef logic [WIDTH-1:0] matrix_t [DIM-1:0][DIM-1:0];

localparam matrix_t zero_mat = '{default: '{default: '0}};

logic clk, rst;

// clk generator
initial clk = 0;
always #5 clk = ~clk;

// rst gennerator
initial begin
    rst = 1;
    repeat (2) @(posedge clk);
    rst = 0;
end

// interface to DUT (device under test)
logic done;
logic [127:0] vector;
matrix_t result;

function automatic matrix_t vec2mat (input logic [WIDTH*DIM*DIM-1:0] vec);
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

// golden model
localparam N = 17;
logic [WIDTH*DIM*DIM-1:0] golden_model [0:N-1];
matrix_t correct_mix_out;
logic is_mistake;

initial begin
    $readmemb("/users_home/eyalroth/Lab_2/TB/golden_model_questa_out.memb", golden_model);
end

// instnatiate DUT
fsm dut ( .clk_i(clk), .rst_i(rst), .vec_i(vector), .mix_out({>>{result}}), .done_out(done));

// scoreboard
int passed = 0;
int failed = 0;

// -----------
//    BFM
// -----------
task automatic send_transaction(input [127:0] vec_i);
    // prepare data safely before rising edge
    @(negedge clk);
    vector = vec_i;
    rst = 1'b1;

    // FSM samples here
    @(posedge clk);
    rst = 1'b0;
endtask


// -------------
// test sequnce
// -------------
initial begin
    int i;
    vector = '0;

    @(negedge rst);

    /* randomized tests */
    $display("Starting random test...");
    for (i = 0; i < N; i++) begin
        if (i == 15) begin
            vector = '0;
        end
        else if (i == 16) begin
            vector = '1;
        end
        else begin
            vector = {$urandom(),$urandom(),$urandom(),$urandom()};
        end
        $display("Sending random vector %0d: %h", i, vector);
        send_transaction(vector);
	//repeat (2) @(posedge clk);
	// introduce idle time for clock gating power improvemints
        repeat (50) @posedge clk);
	correct_mix_out = vec2mat(golden_model[i]);
        wait(done);
        is_mistake = (correct_mix_out != result);
	$display("Is mistake = %0d", is_mistake);
        if (is_mistake) begin
            failed = failed +1;
        end
        else begin
            passed = passed +1;
        end
        @(posedge clk);
    end

    $display("TEST FINISHED!");
    $finish;
end

// --------------
//   Assersions
// --------------

/* When in RESET all outputs / registers must be 0 */
/*
property check_reset_clears_output;
    @(posedge clk)
    //disable iff (!rst)
    (dut.state == dut.RESET) |=> (dut.mix_out == zero_mat && dut.done_out == 0);
endproperty

assert property (check_reset_clears_output)
    else $error("[Assertion failed] Outputs are not 0 during RESET state.");
*/
/* When done is high state shoud be CASE_3 */
/*
property check_done_on_case_3;
    @(posedge clk)
    disable iff (rst)
    (dut.state == dut.CASE_3) |=> dut.done_out;
endproperty

assert property (check_done_on_case_3)
    else $error("[Assertion failed] 'done' is high, but FSM is not in CASE_3.");
*/
/* After state CASE_2 should come state CASE_3 */
/*
property check_fsm_transition;
    @(posedge clk)
    disable iff (rst)
    (dut.state == dut.CASE_2) |=> (dut.state == dut.CASE_3);
endproperty

assert property (check_fsm_transition)
    else $error("[Assertion failed] FSM did not transition from CASE_2 to CASE_3.");


// ------------
//   Coverage
// ------------
covergroup fsm_states @(posedge clk);
    coverpoint dut.state {
        bins reset_fsm  = {dut.RESET};
        bins case_1_fsm = {dut.CASE_1};
        bins case_2_fsm = {dut.CASE_2};
        bins case_3_fsm = {dut.CASE_3};
    }
endgroup

covergroup fsm_transitions @(posedge clk);
    coverpoint dut.state {
        bins reset_to_case_1   = (dut.RESET  => dut.CASE_1);
        bins case_1_to_case_2  = (dut.CASE_1 => dut.CASE_2);
        bins case_2_to_case_3  = (dut.CASE_2 => dut.CASE_3);
        bins case_3_to_reset   = (dut.CASE_3 => dut.RESET);
    }
endgroup

fsm_states      cg_states = new();
fsm_transitions cg_trans  = new();
*/
endmodule
