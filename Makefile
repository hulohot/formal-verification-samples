# Formal Verification Samples Makefile

# Directory structure
DESIGN_DIR  := designs
FORMAL_DIR  := formal
TEST_DIR    := tests
SCRIPT_DIR  := scripts

# Tools
SBY        := sby
VERILATOR  := verilator

# Design targets
DESIGNS     := adder alu arbiter fifo multiplier sequence_detector traffic_light
FORMAL_DIRS := $(addprefix $(FORMAL_DIR)/,$(DESIGNS))

# Default target
.PHONY: all
all: formal

# Create formal verification directories
$(FORMAL_DIRS):
	mkdir -p $@

# Formal verification targets for individual designs
.PHONY: $(addprefix formal_,$(DESIGNS))
$(addprefix formal_,$(DESIGNS)): formal_%: $(FORMAL_DIR)/%
	cd $(FORMAL_DIR)/$* && $(SBY) -f $*.sby

# Run formal verification on all designs
.PHONY: formal
formal: $(addprefix formal_,$(DESIGNS))

# Clean build artifacts
.PHONY: clean
clean:
	rm -rf $(FORMAL_DIR)/*/
	find . -name "*.vcd" -delete
	find . -name "*.log" -delete

# Print available targets
.PHONY: help
help:
	@echo "Available targets:"
	@echo "  make all          - Run all verifications"
	@echo "  make formal       - Run formal verification on all designs"
	@echo "  make formal_NAME  - Run formal verification on specific design"
	@echo "  make clean        - Remove build artifacts"
	@echo ""
	@echo "Available designs:"
	@for design in $(DESIGNS); do \
		echo "  $$design"; \
	done 