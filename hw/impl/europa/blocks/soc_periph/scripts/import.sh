
mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_axi
cp soc_periph_dw_peripherals/components/soc_periph_dw_axi/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_axi

mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_gpio
cp soc_periph_dw_peripherals/components/soc_periph_dw_gpio/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_gpio

mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_uart
cp soc_periph_dw_peripherals/components/soc_periph_dw_uart/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_uart

mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_i2c_0
cp soc_periph_dw_peripherals/components/soc_periph_dw_i2c_0/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_i2c_0

mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_i2c_1
cp soc_periph_dw_peripherals/components/soc_periph_dw_i2c_1/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_i2c_1

mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_ssi
cp soc_periph_dw_peripherals/components/soc_periph_dw_ssi/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_ssi

mkdir -p rtl/soc_periph_dw_peripherals/soc_periph_dw_timers
cp soc_periph_dw_peripherals/components/soc_periph_dw_timers/src/* rtl/soc_periph_dw_peripherals/soc_periph_dw_timers

cp soc_periph_dw_peripherals/components/*/doc/*.pdf docs

cp soc_periph_dw_peripherals/src/soc_periph_dw_peripherals.sv rtl/soc_periph_dw_peripherals/soc_periph_dw_peripherals.sv
