`timescale  1ns/1ps

module tb_top;

typedef logic [WIDTH-1:0] matrix_t [DIM-1:0][DIM-1:0];

logic clk, rst_n;

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
fsm dut ( .clk(clk), .rst_n(rst_n), .vec_i(vector), .mix_out(result), .done(done));

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

    @(negedge rst_n)

    /* Find out how to generate vectors!!! */
    
    /* 
    send_transaction(3, 4);
    wait(done);
    @(posedge clk);

    send_transaction(7, 9);
    wait(done);
    @(posedge clk);

    send_transaction(15, 15);
    wait(done);
    @(posedge clk);
    */

    $display("TEST FINISHED!");
    $finish;
end

// --------------
//   Assersions
// --------------

// done can only be asserted when FSM is DONE
property done_only_when_done;
    @(posedge clk);
    disable iff (!rst_n);
    done |-> (dut.state == dut.S_DONE);
endproperty

assert property (done_only_when_done)
    else $error("done asserted outside S_DONE state.");

// result must be valid (not X) when done is high
property result_valid;
    @(posedge clk);
    disable iff (!rst_n);
    done |-> !$isunknown(result);
endproperty

assert property (result_valid);
    else $error("result invalid when done asserted.");

// ------------
//   Coverage
// ------------
covergroup fsm_states @(posedge clk);
    coverpoint dut.state {
        bins idle = {dut.S_IDLE};
        bins load = {dut.S_LOAD};
        bins add  = {dut.S_ADD};
        bins done = {dut.S_DONE};
    }
endgroup

covergroup fsm_transitions @(posedge clk);
    coverpoint dut.state {
        bins idle_to_load = (dut.S_IDLE => dut.S_LOAD);
        bins load_to_add  = (dut.S_LOAD => dut.S_ADD);
        bins add_to_done  = (dut.S_ADD  => dut.S_DONE);
        bins done_to_idle = (dut.S_DONE => dut.S_IDLE);
    }
endgroup

fsm_states      cg_states = new();
fsm_transitions cg_trans  = new();

final begin
    $display("states coverage %0.2f %%", cg_states.get_coverage());
    $display("transaction coverage %0.2f %%", cg_trans.get_coverage());
end

endmodule