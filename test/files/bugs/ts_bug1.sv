// verilog-ts-mode indentation bug:
// Snippet from axi_test.sv:2008
//   If running (indent-region (point-min) (point-max)) it will indent wrongly
//   until line 15 (wait (this.b_queue[id].size() > 0);) is indented with more than 0.
//   Seem an error of the grammar.
//   Can be workedaround reindenting it twice.

class asdf;

/// Handle Write response checking, update golden model
protected task automatic handle_write_resp(input axi_id_t id);
ax_beat_t  aw_beat;
b_beat_t   b_beat;
axi_addr_t bus_address;
forever begin
wait (this.b_sample[id].size() > 0);
assert (this.b_queue[id].size() > 0) else
wait (this.b_queue[id].size() > 0);
aw_beat = b_queue[id].pop_front();
b_beat  = b_sample[id].pop_front();
if (check_en[BRespCheck]) begin
assert (b_beat.b_id   == id);
end
// pop all accessed memory locations by this beat
for (int unsigned i = 0; i <= aw_beat.ax_len; i++) begin
bus_address = axi_pkg::aligned_addr(
axi_pkg::beat_addr(aw_beat.ax_addr, aw_beat.ax_size, aw_beat.ax_len, aw_beat.ax_burst,
i), BUS_SIZE);
for (int j = 0; j < axi_pkg::num_bytes(BUS_SIZE); j++) begin
if (b_beat.b_resp inside {axi_pkg::RESP_OKAY, axi_pkg::RESP_EXOKAY}) begin
memory_q[bus_address+j].delete(0);
end else begin
memory_q[bus_address+j].delete(memory_q[bus_address+j].size() - 1);
end
end
end
end
endtask : handle_write_resp

endclass;
