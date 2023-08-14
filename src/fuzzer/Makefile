OS = Unknown
ifneq ($(shell uname -a | grep -i Darwin),)
	OS = MacOS
endif
ifneq ($(shell uname -a | grep -i Linux),)
	OS = Linux
endif
ifeq ($(OS),Unknown)
	echo "error: unsupported OS"; exit 1
endif
NPROC?=$(shell nproc)
CC=clang
LLVM_PROFDATA=llvm-profdata
LLVM_COV=llvm-cov
CORPUS_DIR=corpus
FUZZER_FLAGS=-g -O1 -fsanitize=fuzzer,address,undefined -fsanitize-recover=address -DWITH_STDLIB
COVERAGE_DIR=corpus-coverage
COVERAGE_FLAGS=-fprofile-instr-generate -fcoverage-mapping -DWITH_STDLIB
SRCS=../curves/*.c ../external_deps/*.c ../fp/*.c ../hash/*.c ../nn/*.c ../sig/*.c ../utils/*.c
ifeq ($(OS),MacOS)
	COVERAGE_FLAGS+=-Wl,-U,_LLVMFuzzerCustomMutator -Wl,-U,_LLVMFuzzerInitialize
endif

all: fuzzer coverage

fuzzer:
	$(CC) $(FUZZER_FLAGS) -o fuzzer fuzzer.c $(SRCS)

fuzzer-run:
	./fuzzer -len_control=2 -max_len=128 -workers=$(NPROC) -jobs=$(NPROC) $(CORPUS_DIR)

coverage:
	clang $(COVERAGE_FLAGS) -o coverage coverage.c fuzzer.c $(SRCS)

show: $(COVERAGE_DIR)/fuzzer.profdata
	$(LLVM_COV) show --instr-profile=$(COVERAGE_DIR)/fuzzer.profdata coverage

report: coverage $(COVERAGE_DIR)/fuzzer.profdata
	$(LLVM_COV) report --show-functions --instr-profile=$(COVERAGE_DIR)/fuzzer.profdata coverage $(SRCS)

%.profraw: coverage
	LLVM_PROFILE_FILE=$@ ./coverage $(CORPUS_DIR)/*

%.profdata: %.profraw
	$(LLVM_PROFDATA) merge --sparse $< -o $@

clean:
	rm -rf coverage fuzzer *.log

.PHONY: all fuzzer fuzzer-run show coverage report

.PRECIOUS: $(COVERAGE_DIR)/fuzzer.profraw $(COVERAGE_DIR)/fuzzer.profdata
