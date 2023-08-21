// test/files/common/axi_test.sv:1568

// Lacks good support for function/method calls

class axi_lite_rand_master;

    task automatic recv_rs(input int unsigned n_reads);
      automatic addr_t          ar_addr;
      automatic data_t           r_data;
      automatic axi_pkg::resp_t  r_resp;
      repeat (n_reads) begin
        wait (ar_queue.size() > 0);
        ar_addr = this.ar_queue.pop_front();
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.recv_r(r_data, r_resp);
        $display("%0t %s> Recv  R with DATA: %h RESP: %0h", $time(), this.name, r_data, r_resp);
      end
    endtask : recv_rs

    task automatic send_aws(input int unsigned n_writes);
      automatic addr_t aw_addr;
      automatic prot_t aw_prot;
      repeat (n_writes) begin
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        aw_addr = addr_t'($urandom_range(MIN_ADDR, MAX_ADDR));
        aw_prot = prot_t'($urandom());
        this.aw_queue.push_back(aw_addr);
        $display("%0t %s> Send AW with ADDR: %h PROT: %b", $time(), this.name, aw_addr, aw_prot);
        this.drv.send_aw(aw_addr, aw_prot);
        this.b_queue.push_back(1'b1);
      end
    endtask : send_aws

    task automatic send_ws(input int unsigned n_writes);
      automatic logic  rand_success;
      automatic addr_t aw_addr;
      automatic data_t w_data;
      automatic strb_t w_strb;
      repeat (n_writes) begin
        wait (aw_queue.size() > 0);
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        aw_addr = aw_queue.pop_front();
        rand_success = std::randomize(w_data); assert(rand_success);
        rand_success = std::randomize(w_strb); assert(rand_success);
        $display("%0t %s> Send  W with DATA: %h STRB: %h", $time(), this.name, w_data, w_strb);
        this.drv.send_w(w_data, w_strb);
        w_queue.push_back(1'b1);
      end
    endtask : send_ws

    task automatic recv_bs(input int unsigned n_writes);
      automatic logic           go_b;
      automatic axi_pkg::resp_t b_resp;
      repeat (n_writes) begin
        wait (b_queue.size() > 0 && w_queue.size() > 0);
        go_b = this.b_queue.pop_front();
        go_b = this.w_queue.pop_front();
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        this.drv.recv_b(b_resp);
        $display("%0t %s> Recv  B with RESP: %h", $time(), this.name, b_resp);
      end
    endtask : recv_bs

    task automatic run(input int unsigned n_reads, input int unsigned n_writes);
      $display("Run for Reads %0d, Writes %0d", n_reads, n_writes);
      fork
        send_ars(n_reads);
        recv_rs(n_reads);
        send_aws(n_writes);
        send_ws(n_writes);
        recv_bs(n_writes);
      join
    endtask

    // write data to a specific address
    task automatic write(input addr_t w_addr, input prot_t w_prot = prot_t'(0), input data_t w_data,
                         input strb_t w_strb, output axi_pkg::resp_t b_resp);
      $display("%0t %s> Write to ADDR: %h, PROT: %b DATA: %h, STRB: %h",
          $time(), this.name, w_addr, w_prot, w_data, w_strb);
      fork
        this.drv.send_aw(w_addr, w_prot);
        this.drv.send_w(w_data, w_strb);
      join
      this.drv.recv_b(b_resp);
      $display("%0t %s> Received write response from ADDR: %h RESP: %h",
          $time(), this.name, w_addr, b_resp);
    endtask : write

    // read data from a specific location
    task automatic read(input addr_t r_addr, input prot_t r_prot = prot_t'(0),
                        output data_t r_data, output axi_pkg::resp_t r_resp);
      $display("%0t %s> Read from ADDR: %h PROT: %b",
          $time(), this.name, r_addr, r_prot);
      this.drv.send_ar(r_addr, r_prot);
      this.drv.recv_r(r_data, r_resp);
      $display("%0t %s> Recieved read response from ADDR: %h DATA: %h RESP: %h",
          $time(), this.name, r_addr, r_data, r_resp);
    endtask : read

endclass

