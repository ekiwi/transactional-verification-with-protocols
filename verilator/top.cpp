#include <iostream>
#include <sstream>
#include <verilated.h>
#if VM_TRACE
# include <verilated_vcd_c.h>	// Trace file format header
#endif

static bool step0 = true;

#include "top.hpp"

vluint64_t main_time = 0;
VerilatedVcdC* tfp = nullptr;




static void step() {
	step0 = false;
	top->TOP_CLK = 0;
	top->eval();
#if VM_TRACE
	if (tfp) { tfp->dump(main_time); }
#endif
	main_time += 1;
	top->TOP_CLK = 1;
	top->eval();
#if VM_TRACE
	if (tfp) { tfp->dump(main_time); }
#endif
	main_time += 1;
}

static std::vector<std::string> split(const std::string& line, char split_char) {
	std::istringstream f(line);
	std::string s;
	std::vector<std::string> res;
	while(std::getline(f, s, split_char)) {
		res.push_back(s);
	}
	return res;
}

static bool parse_line(const std::string& line) {
	bool running = true;

	auto parts = split(line, ' ');
	assert(parts.size() <= 3);
	assert(parts.size() > 0);
	if(parts[0] == "set") {
		assert(parts.size() == 3);
		set(parts[1], parts[2]);
		return true;
	}
	if(parts[0] == "step") {
		assert(parts.size() == 1);
		step();
		return true;
	}
	if(parts[0] == "exit") {
		assert(parts.size() == 1);
		return false;
	}
	throw new std::runtime_error("Unknonw command: " + line);
}

static bool read_line() {
	std::string line;
	std::getline(std::cin, line);
	return parse_line(line);
}

int main(int argc, char** argv) {

	top = new TOP_TYPE;

#if VM_TRACE
	//std::cout << "Tracing to dump.vcd" << std::endl;
	Verilated::traceEverOn(true);
	tfp = new VerilatedVcdC;
	top->trace(tfp, 99);
	tfp->open ("dump.vcd");
#endif

	while(read_line())
		;

	// finish last cycle
	top->eval();
#if VM_TRACE
	if (tfp) { tfp->dump(main_time); }
	if (tfp) { tfp->close(); }
#endif
}
