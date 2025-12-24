`timescale  1ns/1ps

module tb_top;

typedef logic [WIDTH-1:0] matrix_t [DIM-1:0][DIM-1:0];

logic clk, rst;

// clk generator
initial clk = 0;
always #5 clk = ~clk;

// rst gennerator
initial begin
    rst_n = 1;
    repeat (2) @(posedge clk);
    rst_n = 0;
end

// interface to DUT (device under test)
logic done;
logic [127:0] vector;
miatrix_t result;

// instnatiate DUT
fsm dut ( .clk_i(clk), .rst_i(rst), .vec_i(vector), .mix_out(result), .done(done));

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
endtask;


// -------------
// test sequnce
// -------------
initial begin
    a = 0; b = 0;
    vector = '0;
    int i;

    @(negedge rst)

    /* randomized tests */
    $disable("Starting random test...");
    for (i = 0; i < 15; i++) begin
        if (!std::randomized(vector)) begin
            $error("Randomization failed.");
        end
        $disable("Sending random vector %0d: &h", i, vector);
        send_transaction(vector);
        repeat (2) @(posedge clk);
        wait(done);
        @(posedge clk);
    end

    $display("TEST FINISHED!");
    $finish;
end

// --------------
//   Assersions
// --------------

// done can only be asserted when FSM is DONE
property done_only_when_done;
    @(posedge clk);
    disable iff (!rst);
    done |-> (dut.state == dut.S_DONE);
endproperty

assert property (done_only_when_done)
    else $error("done asserted outside S_DONE state.");

// result must be valid (not X) when done is high
property result_valid;
    @(posedge clk);
    disable iff (!rst);
    done |-> !$isunknown(result);
endproperty

assert property (result_valid);
    else $error("result invalid when done asserted.");

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

final begin
    $display("states coverage %0.2f %%", cg_states.get_coverage());
    $display("transaction coverage %0.2f %%", cg_trans.get_coverage());
end

endmodule