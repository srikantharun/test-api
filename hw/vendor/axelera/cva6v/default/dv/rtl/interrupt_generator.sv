module interrupt_generator (
  input logic clk_i,
  input bit begin_irq_driving,
  input bit end_irq_driving,
  output logic [1:0] irq_tb_line // machine/supervisor interrupts
);

  // Time unit and precision
  timeunit 1ps; timeprecision 1ps;

  typedef enum int {
    VERY_SHORT = 0,
    SHORT = 1,
    NORMAL = 2,
    LONG = 3
  } irq_timing_t;

  int irq_number = 0;
  irq_timing_t irq_delay_timing = NORMAL;
  irq_timing_t irq_width_timing = NORMAL;

  initial begin
    string delay_plusarg, width_plusarg;

    // Parse IRQ_DELAY from the plusargs
    if ($value$plusargs("IRQ_DELAY=%s", delay_plusarg)) begin
      case (delay_plusarg)
        "VERY_SHORT": irq_delay_timing = VERY_SHORT;
        "SHORT": irq_delay_timing = SHORT;
        "NORMAL": irq_delay_timing = NORMAL;
        "LONG": irq_delay_timing = LONG;
        default: $fatal("Invalid IRQ_DELAY value: %s", delay_plusarg);
      endcase
    end

    // Parse IRQ_WIDTH from the plusargs
    if ($value$plusargs("IRQ_WIDTH=%s", width_plusarg)) begin
      case (width_plusarg)
        "VERY_SHORT": irq_width_timing = VERY_SHORT;
        "SHORT": irq_width_timing = SHORT;
        "NORMAL": irq_width_timing = NORMAL;
        "LONG": irq_width_timing = LONG;
        default: $fatal("Invalid IRQ_WIDTH value: %s", width_plusarg);
      endcase
    end
  end


  // IRQs
  assign irq_tb_line = '0;
  initial begin
    bit [1:0] irq_value = '0;
    int irq_delay, irq_width;

    if ($test$plusargs("enable_irqs")) begin
      $display("[IRQ]s enabled!");
      $display("IRQ_DELAY set to: %s", irq_delay_timing.name());
      $display("IRQ_WIDTH set to: %s", irq_width_timing.name());
      // Wait for .word 0 -> end of init
      wait(begin_irq_driving);

      // IRQ driving proc (until end of test is reached)
      fork
        begin
          forever begin
            // Randomize delay (time between IRQ events) and width (duration of IRQ pulse)
            case (irq_delay_timing)
                VERY_SHORT:  assert(std::randomize(irq_delay) with {irq_delay inside {[1:500]};});
                SHORT:  assert(std::randomize(irq_delay) with {irq_delay inside {[500:2000]};});
                NORMAL: assert(std::randomize(irq_delay) with {irq_delay inside {[2000:5000]};});
                LONG:   assert(std::randomize(irq_delay) with {irq_delay inside {[5000:13000]};});
            endcase
            case (irq_width_timing)
              VERY_SHORT:  assert(std::randomize(irq_width) with {irq_width inside {[50:150]};});
              SHORT:  assert(std::randomize(irq_width) with {irq_width inside {[100:300]};});
              NORMAL: assert(std::randomize(irq_width) with {irq_width inside {[300:500]};});
              LONG:   assert(std::randomize(irq_width) with {irq_width inside {[500:1000]};});
            endcase

            repeat (irq_delay) @(posedge clk_i);

            assert(
              std::randomize(irq_value) with {irq_value dist {2'b11 := 10, 2'b10 := 30, 2'b01 := 60};}
            );

            $display("[%t] [IRQ] no %0d, width %0d, value %0h \n Wait %0d afterwards", $time, irq_number, irq_width, irq_value, irq_delay);

            force irq_tb_line = irq_value;

            repeat (irq_width)  @(posedge clk_i);

            release irq_tb_line;
            irq_number++;
          end
        end

        // End of test monitoring to stop IRQ generation
        begin
          wait (end_irq_driving);
            $display("[%t] [IRQ] ECALL detected ending MIRQ driving", $time);
            release irq_tb_line;
        end
      join_any
      disable fork;
    end
  end

endmodule : interrupt_generator
