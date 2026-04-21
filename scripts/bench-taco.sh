#!/bin/bash
# TACO benchmarking script 
IFS=$'\n\t'


################################################################################
### Configurable Environment Variables
################################################################################

# Timeout per benchmark
TIMEOUT="${TIMEOUT:=20m}"
# Name of the files that will be created 
OUTFILE_NAME="${OUTFILE_NAME:=taco-exec}"
# Directory to move log files and crash reports to
OUTDIR="${OUTDIR:=/storage}"
# Only execute smoke tests
SMOKE_TEST_ONLY="${SMOKE_TEST_ONLY:=false}"
# Print model checker output to stdout instead of creating a log file
LOG_TO_STDOUT="${LOG_TO_STDOUT:=false}"
# Stop checking benchmarks if an error occurs
FAIL_ON_ERROR="${FAIL_ON_ERROR:=false}"
# Benchmark directory
BENCHMARK_DIR="${BENCHMARK_DIR:=./benchmarks}"
# TACO executable
EXECUTABLE="${EXECUTABLE:=taco-cli}"
# SMT Solver
SMT_SOLVER="${SMT_SOLVER:=z3}"
# Memory limit (on the virtual memory) in MB
MEM_LIMIT="${MEM_LIMIT:=unlimited}"
# Configure whether to run the specified model checkers on the extended set of
# benchmarks
EXTENDED="${EXTENDED:=false}"


################################################################################
### Fixed helper variables
################################################################################

# Temporary file capturing timing statistics
TMP_TIME_FILE=$(mktemp)

ACS=false
ZCS=false
SMT=false

RESET_ONLY=false

# Format that this script can parse / will output
TIMEFORMAT="time: %e s, max RSS: %M KB"

GNU_TIME_FOUND=false
PYTHON_FOUND=false
AWK_FOUND=false

# Logfile to write model checker output to
LOGFILE="${OUTFILE_NAME}.log"
# CSV file to write the benchmark results to
CSV_FILE_NAME="${OUTFILE_NAME}.csv"


################################################################################
### Pre-benchmark run initialization
################################################################################

# Terminate all benchmark executions directly when receiving SIGTERM or SIGINT
exit_script () {
    printf "\nTermination signal received\n" | tee -a "${LOGFILE}"
    trap - SIGINT SIGTERM # clear the trap
    kill -- -$$ # Sends SIGTERM to child/sub processes
} 
trap exit_script SIGINT SIGTERM

# Use GNU time if available
if [ -x /usr/bin/time ]; then
    TIME_CMD="/usr/bin/time"
    GNU_TIME_FOUND=true
else
    printf "GNU time not detected. Cannot create result table, as output of \
time might be unstable. You will have to parse the results manually.\n\n"  1>&2
    TIME_CMD="time"
fi

# Check if python is available
if command -v python3 &>/dev/null; then 
    PYTHON_FOUND=true
else 
    printf "Python3 not found. Cannot create result table. You will have \
to parse the results manually.\n\n"  1>&2
fi

# Check if awk is available
if command -v awk &>/dev/null; then 
    AWK_FOUND=true
else 
    printf "awk not found. Cannot create result table. You will have \
to parse the results manually.\n\n"  1>&2
fi


################################################################################
### Helper functions
################################################################################

# Write an entry to csv
#
# This function can add and entry to a csv file. It will only execute if all 
# prerequisites are met, i.e., when
#   - Python3 is installed and accessible by executing `python3`
#   - The GNU time command is available and installed in `/usr/bin/time`
#
# Arguments:
#   1. row (named by first entry)
#   2. column (by name)
#   3. value to insert
write_row_column_csv() {
    if [ "${PYTHON_FOUND}" = true ] && [ "${GNU_TIME_FOUND}" = true ] ; then 
        local file="${CSV_FILE_NAME}"
        local row="${1}"
        local col="${2}"
        local val="${3}"
        
        python3 - "$file" "$row" "$col" "$val" <<'PYCSV'
import csv, sys, os

file, bench, col, val = sys.argv[1:5]

rows = []
fieldnames = []

if os.path.exists(file) and os.path.getsize(file) > 0:
    with open(file, newline='') as f:
        r = csv.DictReader(f)
        fieldnames = (r.fieldnames or [])
        rows = list(r)
else:
    fieldnames = ['benchmark']
    rows = []

# Ensure the column exists
if col not in fieldnames:
    fieldnames.append(col)

# Find or create the row
row = None
for r in rows:
    if (r.get('benchmark') or '') == bench:
        row = r
        break

if row is None:
    row = {'benchmark': bench}
    rows.append(row)

# Update the value
row[col] = val

# Write back, preserving all other cells
with open(file, 'w', newline='') as f:
    w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')
    w.writeheader()
    for r in rows:
        for k in fieldnames:
            r.setdefault(k, '')
        w.writerow(r)
PYCSV
    fi
}


################################################################################
### Benchmarking functions
################################################################################

# Writes memory consumption and execution time as well as safe / unsafe to csv
#
# Arguments: 
#   1. Benchmark file 
#   2. Model checker
#   3. Execution time 
#   4. Memory consumption 
#   5. safe / unsafe 
write_taco_bench_res () {
    # write the safe column first
    if [ ! -z "${5}" ]; then
        # Write save / unsafe 
        write_row_column_csv "${1}" "safe?" "${5}"
    fi

    # Write exec time 
    write_row_column_csv "${1}" "${2}-${SMT_SOLVER}-time(s)" "${3}"
    # Write mem consumption 
    write_row_column_csv "${1}" "${2}-${SMT_SOLVER}-mem(GB)" "${4}"
}

# Attempts to parse the number of locations and the number of rules of the 
# threshold automaton by parsing the output of TACO
#
# Warning: This function is somewhat brittle. It searches for the last 
#  occurrence of a statement of the form
#  'Threshold automaton has <N_LOC> locations and <N_RULES> rules' in $LOGFILE
#  file output and takes the result from there. It does not validate whether
#  this comes from the last model checking run. This can cause problems if for
#  example the input file had a syntax error and no automaton could be parsed
#
# Arguments:
#   1. Benchmark file 
parse_and_write_n_rules_locations () {

    # If LOG_TO_STDOUT then we cannot pares the number of locations and rules 
    # because we cannot read back log file. This check prevents error messages.
    if [ "${LOG_TO_STDOUT}" = true ]; then 
        printf "Skipping parsing number of locations and rules as logs are sent to stdout\n"
        return 0
    fi


    local n_rules 

    local n_locations 

    # Search for the last occurrence of the pattern:
    # 'Threshold automaton has <N_LOC> locations and <N_RULES> rules'
    local line
    line="$(grep "Threshold automaton has.*locations and.*rules" "${LOGFILE}" 2>/dev/null | tail -n 1)"

    # Parse number of locations
    if [[ "${line}" =~ Threshold[[:space:]]+automaton[[:space:]]+has[[:space:]]+([0-9]+)[[:space:]]+locations ]]; then
        n_locations="${BASH_REMATCH[1]}"
    fi

    # Parse number of rules
    if [[ "${line}" =~ locations[[:space:]]+and[[:space:]]+([0-9]+)[[:space:]]+rules ]]; then
        n_rules="${BASH_REMATCH[1]}"
    fi

    if [ ! -z "${n_rules}" ]; then
        write_row_column_csv "${1}" "|Rules|" "${n_rules}"
    else 
        printf "Failed to parse number of rules for benchmark '${1}'\n"
    fi

    if [ ! -z "${n_locations}" ]; then
        write_row_column_csv "${1}" "|Locations|" "${n_locations}"
    else 
        printf "Failed to parse number of locations for benchmark '${1}'\n"
    fi
}

# Parses execution time, memory consumption and result of the model checker and 
# writes them to stdout and the 
# 
# Arguments:
#   1. Benchmark file 
#   2. model checker
process_exec_time_and_mc_result () {
    # Safe / Unsafe
    local mcres 
    # tail -n 2: last two lines
    # head -n 1: the first of those (i.e., second-to-last in file)
    # tr -d '\r': strip CR if file is CRLF
    local line
    # If logfile has fewer than 2 lines, this will be empty
    line="$(tail -n 2 -- "${LOGFILE}" 2>/dev/null | head -n 1 | tr -d '\r')"

    if grep -Fq "The protocol is safe." <<<"$line"; then
        printf "Model checker '${2}' determined '${1}' to be safe.\n"
        mcres="safe"
    elif grep -Fq "The protocol is unsafe." <<<"$line"; then
        printf "Model checker '${2}' determined '${1}' to be unsafe.\n"
        mcres="unsafe"
    fi
    
    # Read the output of time from the temp file and write it to stdout and the
    # log file
    cat "${TMP_TIME_FILE}" | tee -a "${LOGFILE}"

    # Parse time 
    local time_s rss_value rss_kb
    # Read the last line of the temp file 
    line="$(tail -n 1 -- "${TMP_TIME_FILE}" 2>/dev/null | tr -d '\r')"

    # Extract time seconds (float)
    if [[ "${line}" =~ time:[[:space:]]*([0-9]*\.?[0-9]+)[[:space:]]*s ]]; then
        time_s="${BASH_REMATCH[1]}"
    fi

    # Extract RSS in KB
    if [[ "${line}" =~ max[[:space:]]+RSS:[[:space:]]*([0-9]+)[[:space:]]*KB ]]; then
        rss_kb="${BASH_REMATCH[1]}"
    fi

    # Convert KB to GB 
    if [ "${AWK_FOUND}" = true ]; then
        # GB = KB / (1024 * 1024)
        rss_value=$(awk -v kb="$rss_kb" 'BEGIN {
            gb = kb / (1024 * 1024);
            gb_r = int(gb * 100) / 100 
            printf "%.2f\n", gb
        }')
    else 
        # if awk is not available write the KB result
        rss_value="${rss_kb}KB"
    fi

    write_taco_bench_res "${1}" "${2}" "${time_s}" "${rss_value}" "${mcres}"
}


# Process benchmark exit codes
#
# This function is designed to process return codes that are not 0 of a 
# benchmark checker run. It determines whether the benchmark timed out, an error
# occurred or a 
# 
# Arguments:
#   1. exit code of the benchmark run
#   2. model checker that has been used
#   3. benchmark file that has been checked
process_return_not_zero () {
    # Read the output of time from the temp file and write it to stdout and the
    # log file
    cat "${TMP_TIME_FILE}" >> "${LOGFILE}"

    # Process return code of `timeout`
    if [ "${1}" -eq 124 ]; then
        # Timeout has occurred
        printf "TIMEOUT for model checker '${3}' on '${2}'\n" | tee -a "${LOGFILE}"
        write_taco_bench_res "${2}" "${3}" "TO" "-" ""
    elif [ "${1}" -eq 139 ] && [ ! "${MEM_LIMIT}" = "unlimited" ]; then
        # SIGSEV this should only occur once TACO runs into the memory limit
        printf "OOM for model checker '${3}' on '${2}'\n" | tee -a "${LOGFILE}"
        write_taco_bench_res "${2}" "${3}" "OOM" "-" ""
    elif [ "${1}" -gt 124 ] && [ "${1}" -lt 128 ]; then 
        printf "Failed to invoke the 'timeout' command. Timeout returned code '${1}'\n"
        exit "${1}"
    else 
        # must be non zero
        printf "Error: TACO exited with non-zero return code '${1}', \
please check the logs for the location of potential error reports.\n\n" 1>&2

        write_taco_bench_res "${2}" "${3}" "Err" "-" ""

        if [ $FAIL_ON_ERROR = true ]; then 
            # Terminate with the TACO exit code
            exit "${1}" 
        fi
    fi
}


# Benchmark execution function
# 
# This function calls the model checker in the benchmark configuration, i.e.,
# it sets the model checker to abort on a violation ('-a' flag) and explicitly 
# sets the model checker into 
# 
# Arguments:
#   1. benchmark file to be checked
#   2. model checker to be used
run_taco_with_mem_limit() {
    (
        local RET=0
        if [ "${MEM_LIMIT}" != "unlimited" ]; then
            local MEM_LIMIT_KB=$(("${MEM_LIMIT}"*1024))
            ulimit -SHv "${MEM_LIMIT_KB}"
        fi

        if [ "${GNU_TIME_FOUND}" = true ]; then
           { "${TIME_CMD}"  -f "${TIMEFORMAT}" "${EXECUTABLE}" check "${BENCHMARK_DIR}/${1}" -a -o --smt-solver "${SMT_SOLVER}" "${2}" >> "${MC_OUTPUT}";RET=$?; } 2> "${TMP_TIME_FILE}"
        else
            { "${TIME_CMD}" "${EXECUTABLE}" check "${BENCHMARK_DIR}/${1}" -a -o --smt-solver "${SMT_SOLVER}" "${2}" >> "${MC_OUTPUT}";RET=$?; } 2> "${TMP_TIME_FILE}"
        fi
        return "${RET}"
    )
    return $?
}
export -f run_taco_with_mem_limit

# Benchmark execution function
# 
# This function calls the model checker in the benchmark configuration, i.e.,
# it sets the model checker to abort on a violation ('-a' flag) and explicitly 
# sets the model checker into 
# 
# Arguments:
#   1. benchmark file to be checked
#   2. model checker to be used
run_benchmark () {
    printf "Checking benchmark '${1}' with model checker '${2}'\n" | tee -a "${LOGFILE}"

    # Store timeout return code
    local RET=0
    
    # By default model checker output is written to the logfile
    local MC_OUTPUT=${LOGFILE}
    # If LOG_TO_STDOUT is true, set to output to stdout instead
    if [ "${LOG_TO_STDOUT}" = true ]; then 
        MC_OUTPUT="/dev/stdout"
    fi

    # export all necessary environment variables
    export MC_OUTPUT \
        MEM_LIMIT \
        EXECUTABLE \
        BENCHMARK_DIR \
        SMT_SOLVER \
        GNU_TIME_FOUND \
        TIME_CMD \
        TIMEFORMAT \
        TMP_TIME_FILE

    { timeout "${TIMEOUT}" bash -c 'run_taco_with_mem_limit "$@"' -- "${1}" "${2}"; RET=$?; }
   
    parse_and_write_n_rules_locations "${1}"

    if [ "${RET}" -ne 0 ]; then 
        process_return_not_zero "${RET}" "${1}" "${2}"
    else 
        process_exec_time_and_mc_result "${1}" "${2}"
    fi


    printf "\n\n" | tee -a "${LOGFILE}"
}




# Function to run all small BYMC benchmarks
#
# First argument is the model checker to be used, all arguments are passed to 
# `run_benchmarks`
run_small_benchmarks () {
    printf "Checking hand-coded benchmarks with model checker '$1'\n" | tee -a "${LOGFILE}"

    SMALL_BENCH_DIR="TACO/isola18/ta-(handcoded)"

    run_benchmark "${SMALL_BENCH_DIR}/aba.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/bcrb.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/bosco.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/c1cs.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/cc.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/cf1s.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/nbacg.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/nbacr.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/strb.ta" $@

    printf "Finished checking small benchmarks with model checker '$1'\n\n\n" | tee -a "${LOGFILE}"
}


# Function to run all big BYMC benchmarks
#
# First argument is the model checker to be used, all arguments are passed to 
# `run_benchmarks`
run_big_benchmarks () {
    printf "Checking Promela BYMC benchmarks with model checker '${1}'\n" | tee -a "${LOGFILE}"

    BIG_BENCH_DIR="TACO"

    # Exclude benchmarks not part of the main evaluation
    if [ "${EXTENDED}" = true ]; then
        # concur14
        run_benchmark "${BIG_BENCH_DIR}/concur14/asyn-byzagreement0.ta"  $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/asyn-ray97-nbac-clean.ta"  $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/asyn-ray97-nbac.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/bcast-byz.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/bcast-folklore-crash.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/cond-consensus2.ta" $@
        if [ "${1}" = "acs" ]; then 
            printf "*Not* checking '${BIG_BENCH_DIR}/concur14/toy.ta' as it contains a \
    reachability property which is not support by the ACS model checker!\n\n" | tee -a "${LOGFILE}"
            write_taco_bench_res "${BIG_BENCH_DIR}/concur14/toy.ta" "${1}" "Unsup." "-" ""
        else 
            run_benchmark "${BIG_BENCH_DIR}/concur14/toy.ta" $@
        fi

        # cav15
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/aba-asyn-byzagreement0_case1.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/aba-asyn-byzagreement0_case2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/bosco_case1.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/bosco_case2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/bosco_case3.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/c1cs_case1.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/c1cs_case2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/c1cs_case3.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cbc-cond-consensus2_case1.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cbc-cond-consensus2_case2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cbc-cond-consensus2_case3.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cbc-cond-consensus2_case4.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cf1s-consensus-folklore-onestep_case1.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cf1s-consensus-folklore-onestep_case2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/cf1s-consensus-folklore-onestep_case3.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/frb-bcast-folklore-crash.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/nbac-asyn-ray97-nbac.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/nbacc-asyn-ray97-nbac-clean.ta" $@
        if [ "${1}" = "acs" ]; then 
            printf "*Not* checking '${BIG_BENCH_DIR}/cav15/promela/nbacg-asyn-guer01-nbac.ta' as it contains a \
    reachability property which is not support by the ACS model checker!\n\n" | tee -a "${LOGFILE}"
            write_taco_bench_res "${BIG_BENCH_DIR}/cav15/promela/nbacg-asyn-guer01-nbac.ta" "${1}" "Unsup." "-" ""
        else 
            run_benchmark "${BIG_BENCH_DIR}/cav15/promela/nbacg-asyn-guer01-nbac.ta" $@
        fi
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/strb-bcast-byz.ta" $@

        # popl17-fmsd17
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/asyn-byzagreement0.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/asyn-guer01-nbac.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/asyn-ray97-nbac-clean.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/asyn-ray97-nbac.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/bcast-byz.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/bosco.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/c1cs.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/cond-consensus2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/popl17-fmsd17/consensus-folklore-onestep.ta" $@
    fi

    # isola 18
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/aba_case1.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/aba_case2.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/bosco_case1.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/bosco_case2.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/bosco_case3.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/c1cs_case1.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/c1cs_case2.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/c1cs_case3.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cc_case1.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cc_case2.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cc_case3.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cc_case4.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cf1s_case1.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cf1s_case2.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/cf1s_case3.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/frb.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/nbacg.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/nbacr.ta" $@
    run_benchmark "${BIG_BENCH_DIR}/isola18/promela/strb.ta" $@

    # Exclude benchmarks not part of the main evaluation
    if [ "${EXTENDED}" = true ]; then
        #random19
        run_benchmark "${BIG_BENCH_DIR}/random19/ben-or.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-ben-or-byz.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-ben-or-nonclean.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-ben-or.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-kset.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-rabc-cr.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-rabc-s.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-rabc.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/n-rs-bosco.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-ben-or-byz.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-ben-or-nonclean.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-ben-or.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-kset.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-rabc-cr.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-rabc-s.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-rabc.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/random19/p-rs-bosco.ta" $@

        # lmcs20
        run_benchmark "${BIG_BENCH_DIR}/lmcs20/tendermint-1round-safety.ta" $@
    fi
   
    printf "Finished checking big benchmarks with model checker '${1}'\n\n\n" | tee -a "${LOGFILE}"
}


# Function to run all small red-belly benchmarks without resets
#
# First argument is the model checker to be used, all arguments are passed to 
# `run_benchmarks`
run_rb_wo_reset_benchmarks () {
    printf "Checking small RedBelly benchmarks without resets\n" | tee -a "${LOGFILE}"

    RB_SMALL_BENCH_DIR="red-belly"

    run_benchmark "${RB_SMALL_BENCH_DIR}/rb-bc.ta" $@
    run_benchmark "${RB_SMALL_BENCH_DIR}/rb-simple.ta" $@
    run_benchmark "${RB_SMALL_BENCH_DIR}/rb.ta" $@

    printf "Finished checking small red-belly benchmarks without resets with \
model checker '${1}'\n\n\n" | tee -a "${LOGFILE}"
}


# Function to run all king consensus benchmarks (with resets)
#
# First argument is the model checker to be used, all arguments are passed to 
# `run_benchmarks`
run_reset_king_benchmarks () {
     printf "Checking King Consensus benchmarks\n" | tee -a "${LOGFILE}"

    KING_BENCH_DIR="reset-benchmarks"

    run_benchmark "${KING_BENCH_DIR}/phase-king-buggy.eta" $@
    run_benchmark "${KING_BENCH_DIR}/phase-king.eta" $@

    printf "Finished checking king consensus benchmarks with model checker '${1}'\n\n\n" | tee -a "${LOGFILE}"
}


# Function to run all red-bell benchmarks with resets
#
# First argument is the model checker to be used, all arguments are passed to 
# `run_benchmarks`
run_rb_reset_benchmarks () {
    printf "Checking RedBelly with reset benchmarks with model checker '$1'\n" | tee -a "${LOGFILE}"

    RB_RESET_BENCH_DIR="reset-benchmarks"

    run_benchmark "${RB_RESET_BENCH_DIR}/rb-2x_reset.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-floodMin_V0.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-floodMin_V1.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-RelBrd_V1.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-reset_V0.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-reset_V1.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-simple-2x_reset_V0.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-simple-2x_reset_V1.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-simple-reset_V0.eta" $@
    run_benchmark "${RB_RESET_BENCH_DIR}/rb-simple-reset_V1.eta" $@

    printf "Finished checking red-belly with reset benchmarks  with model \
checker '${1}'\n\n\n" | tee -a "${LOGFILE}"
}


# Execute the smoke tests
smoke_tests () {
    printf "Executing the smoke tests

This mode will execute the 'ByMC Handcoded ISOLA18' benchmarks for all of the selected model 
checkers and print the output of the model checker to stdout. All of these 
benchmarks should be reported to be safe, and most benchmark should finish 
within the 30s timeout set for this benchmark run by default.

The 'cc.ta' should definitely timeout for the 'ZCS' and 'ACS' model checkers and 
the 'c1cs.ta' might also timeout for 'ZCS' (and 'ACS') depending on your 
hardware.

(In case all dependencies are met,) this script will also produce a table 
summarizing the results in a CSV file called '${CSV_FILE_NAME}'. The table 
should roughly match the table reported in the paper.
"
    LOGFILE=/dev/null
    FAIL_ON_ERROR=true
    
    # if the default timeout has not been overwritten
    if [ $TIMEOUT = "20m" ]; then 
        TIMEOUT='30s'
    fi

    if [ $SMT = true ]; then 
        run_small_benchmarks smt true
    fi

    if [ $ZCS = true ]; then 
        run_small_benchmarks zcs true
    fi 

    if [ $ACS = true ]; then 
        run_small_benchmarks acs true
    fi 

    printf "\nFinished executing smoke tests\n\n"
}


################################################################################
### Main functionality of the benchmarking script
################################################################################

printf "Welcome to the TACO benchmark script.

Use '--help' or '-h' to see all available options.\n\n"

while [[ $# -gt 0 ]]; do
  case "${1}" in
    -s|--smoke)
        SMOKE_TEST_ONLY=true
        LOG_TO_STDOUT=true
        shift # past value
        ;;
    -t|--timeout)
        TIMEOUT="${2}"
        shift # past argument
        shift # past value
        ;;
    -m|--mem-limit)
        MEM_LIMIT="${2}"
        shift # past argument
        shift # past value
        ;;
    --acs)
        ACS=true
        shift # past argument
        ;;
    --zcs)
        ZCS=true
        shift # past argument
        ;;
    --smt)
        SMT=true
        shift # past argument
        ;;
    -e|--extended)
        EXTENDED=true
        shift # past argument
        ;;
    -r|--reset-only)
        RESET_ONLY=true
        shift
        ;;
    --log-to-stdout)
        LOG_TO_STDOUT=true
        LOGFILE=/dev/null
        shift # past argument
        ;;
    --fail-on-error)
        FAIL_ON_ERROR=true
        shift # past argument
        ;;
    --smt-solver)
        SMT_SOLVER="${2}"
        shift
        shift
        ;;
    -h|--help)
        printf "TACO Benchmark Script help

This is the TACO benchmark script designed to benchmark the TACO model checker.
This scripts supports the following options:
    -h | --help       : Print this message
    -s | --smoke      : Execute a small set of benchmarks for the specified model 
                        checkers (default: all) that should terminate within 5min
    -e | --extended   : Benchmark the full extended set of benchmarks (this can
                        take a lot of time!) 
    -t | --timeout    : Override the per benchmark timeout (default: '20m')
    -r | --reset-only : Only execute reset benchmarks
    --mem-limit | -m : Memory limit for the execution in MB (sets `ulimit -SHv`, 
                       default: unlimited)
    --log-to-stdout   : Print the logs of the model checker to stdout instead of 
                        creating a separate log file (always enabled for smoke
                        tests)
    --fail-on-error   : Stop benchmark execution if an error is encountered
    --smt-solver      : Set the smt solver to 'cvc5' or 'z3' (by default: cvc5)

Additionally, you can also specify which model checker should be benchmark. If 
no flag is passed, all model checkers will be benchmarked. If you specify one or
more model checkers, only the specified model checkers will be benchmarked.
    --acs           : Benchmark the ACS model checker
    --zcs           : Benchmark the ZCS model checker
    --smt           : Benchmark the SMT model checker

The execution time, as well as statistics on memory usage will be printed during
the benchmark execution and additionally stored in a .csv file named 
'taco-exec.log'. The output of the model checker will be stored in the
logfile (by default named 'taco-exec.log'). The name of the logfile and the CSV 
file can be overridden by setting the 'OUTFILE_NAME' env variable.
Both files will be moved to 'OUTDIR' (by default '/storage', can be overridden 
using 'OUTDIR' env variable) after a benchmark run, if the directory exists.

To generate a valid benchmark table, this script requires 'python3', 'awk', and
GNU time to be installed. If a dependency is not met, you will have to parse the
results manually from the logfile (or output of this script).
"
        exit 0
        ;;
    *)
        printf "Unrecognized option '${1}'. Use '--help' / '-h'  for available \
options.\n" 1>&2
        exit -1
        ;;
  esac
done

# Validate solver selection
if [ ! "${SMT_SOLVER}" = "z3" ] && [ ! "${SMT_SOLVER}" = "cvc5" ]; then 
    printf "This benchmarking script only supports z3 or cvc5 as SMT solvers. 
For other SMT solvers you need to call TACO directly.\n" 1>&2
    exit -2
fi

# Print the memory limit
if [ ! "${MEM_LIMIT}" = "unlimited" ]; then
    if [ "${MEM_LIMIT}" -lt 125 ]; then 
        printf "Virtual memory limit less then 125MB not recommended (currently: \
'${MEM_LIMIT}'). Low memory limits can prevent this script from working correctly!\n" 1>&2
        exit -3
    fi

    printf "Memory limit for virtual memory during benchmark executions set to \
${MEM_LIMIT}MB.\n"
fi

# Validate model checker selection with benchmark selection
if [ "${RESET_ONLY}" = true ] && [ "${SMT}" = true ]; then 
    printf "Reset benchmarks not supported by the SMT model checker!\n" 1>&2
    exit -1;
fi

# If no model checker has been selected, select all of them
if [ "${ACS}" = false ] && [ "${ZCS}" = false ] && [ "${SMT}" = false ]; then
    ACS=true
    ZCS=true
    SMT=true
fi

# Test whether permissions are correct on OUTDIR (need write + create of files)
if [ -d "${OUTDIR}" ]; then
    # Verify we can create files in OUTDIR
    OUTDIR_TEST_FILE="${OUTDIR}/.taco-write-test.tmp"
    touch "${OUTDIR_TEST_FILE}"
    if [ ! -f "${OUTDIR_TEST_FILE}" ]; then
        printf "Directory '${OUTDIR}' exists but is not writable / cannot create
files in it. This error might be resolvable by adding :z after the volume mount 
description. Check the README for details.

If you chose to continue anyway, results will stay in the current working 
directory. Sleeping 10s to give you time to abort.\n\n\n
" 1>&2
        OUTDIR=""
        sleep 10
    else
        rm -f "${OUTDIR_TEST_FILE}"
    fi
fi


# Run the smoke tests and exit
if [ $SMOKE_TEST_ONLY = true ]; then 
    smoke_tests 
    exit 0
fi

# Execute the full set of benchmarks
printf "Executing the TACO benchmark suite with SMT solver '${SMT_SOLVER}' and a 
timeout per benchmark of '${TIMEOUT}'.\n\n"

# Make the user aware of extended setting
if [ "${EXTENDED}" = true ]; then
    printf "Executing the extended TACO benchmark suite. This can take a lot of 
    time!\n"
fi

if [ "${SMT}" = true ]; then 
    run_small_benchmarks smt
    run_rb_wo_reset_benchmarks smt
    run_big_benchmarks smt
fi

if [ "${ZCS}" = true ]; then
    if [ "${RESET_ONLY}" = false ]; then
        run_small_benchmarks zcs 
        run_rb_wo_reset_benchmarks zcs 
        run_big_benchmarks zcs 
    fi

    run_reset_king_benchmarks zcs
    run_rb_reset_benchmarks zcs
fi

if [ "${ACS}" = true ]; then 
    if [ "${RESET_ONLY}" = false ]; then
        run_small_benchmarks acs
        run_rb_wo_reset_benchmarks acs
        run_big_benchmarks acs
    fi 

    run_reset_king_benchmarks acs
    run_rb_reset_benchmarks acs
fi 

printf "Finished running all benchmarks\n\n"


# Collect log file and error reports to move them to local storage 
if [ -d "${OUTDIR}" ]; then
    if ls /tmp/report-* 1> /dev/null 2>&1; then
       printf "Found potential crash reports of taco :(. Copying them to local \
storage\n"
        cp /tmp/report-* "${OUTDIR}"
    fi

    printf "Copying the benchmark execution log '${LOGFILE}' to local storage\n"
    cp --backup=t "${LOGFILE}" "${OUTDIR}"
    if [ -f "${CSV_FILE_NAME}" ]; then 
        printf "Copying the benchmark result table '${CSV_FILE_NAME}' to local \
storage\n"
        cp --backup=t "${CSV_FILE_NAME}" "${OUTDIR}"
    fi
else 
    printf "No output directory specified, or directory does not exist.\n" 

    if [ -f "${CSV_FILE_NAME}" ]; then 
        printf "You can find the execution log file '${LOGFILE}' and the \
generated benchmark table '${CSV_FILE_NAME}' in the current directory.\n"
    else 
        printf "You can find the execution log file '${LOGFILE}' and the \
generated benchmark table '${CSV_FILE_NAME}' in the current directory.\n"
    fi

    printf "In case errors occurred, please examine the logfile for the location \
of the generated crash reports.\n"
fi
