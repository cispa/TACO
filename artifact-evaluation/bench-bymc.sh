#!/bin/bash
# ByMC benchmark script
IFS=$'\n\t'

# fix perl complaints
LANG=C


################################################################################
### Configurable Environment Variables
################################################################################
# Timeout per benchmark
TIMEOUT="${TIMEOUT:=20m}"
# Name of the files that will be created 
OUTFILE_NAME="${OUTFILE_NAME:=bymc-exec}"
# Directory to move log files and crash reports to
OUTDIR="${OUTDIR:=/storage}"
# Print model checker output to stdout instead of creating a log file
LOG_TO_STDOUT="${LOG_TO_STDOUT:=false}"
# Benchmark directory
BENCHMARK_DIR="${BENCHMARK_DIR:=./benchmarks}"
# ByMC executable
EXECUTABLE="${EXECUTABLE:=./bymc/verify}"
# Configure whether to run the specified model checkers on the extended set of
# benchmarks
EXTENDED="${EXTENDED:=false}"
# Smoke Test Run
SMOKE="${SMOKE:=false}"


################################################################################
### Fixed helper variables
################################################################################

# Temporary file capturing timing statistics
TMP_TIME_FILE=$(mktemp)

GNU_TIME_FOUND=false
PYTHON_FOUND=false
AWK_FOUND=false

# Logfile to write model checker output to
LOGFILE="${OUTFILE_NAME}.log"
# CSV file to write the benchmark results to
CSV_FILE_NAME="${OUTFILE_NAME}.csv"

# Format that this script can parse / will output
TIMEFORMAT="time: %e s, max RSS: %M KB"


################################################################################
### Pre-benchmark run initialization
################################################################################
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


# Terminate all benchmark executions directly when receiving SIGTERM
exit_script () {
    printf "\nTermination signal received\n" | tee -a "${LOGFILE}"
    trap - TERM INT # clear the trap
    kill -- -$$ # Sends SIGTERM to child/sub processes
} 
trap exit_script TERM INT

# disable warnings
export OMPI_MCA_btl_base_warn_component_unused=0


################################################################################
### Helper functions
################################################################################

# Write an entry to csv
#
# This function can add an entry to a csv file. It will only execute if all 
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
#   2. Execution time 
#   3. Memory consumption 
#   4. Unsafe
#   5. BYMC Mode
write_bymc_bench_res () {
    # Write exec time 
    write_row_column_csv "${1}" "ByMC-${5}-time(s)" "${2}"
    # Write mem consumption 
    write_row_column_csv "${1}" "ByMC-${5}-mem(GB)" "${3}"

    if [ ! -z "${4}" ]; then
        # Write safe / unsafe 
        write_row_column_csv "${1}" "safe?" "${4}"
    fi
}


# Parses execution time and memory consumption in GB
#
# Arguments
#   1. Benchmark file
#   2. Unsafe
#   3. ByMC mode
process_exec_time () {
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

    write_bymc_bench_res "${1}" "${time_s}" "${rss_value}" "${2}" "${3}"
}


# Benchmark execution function
#
# This function calls ByMCs `verify` command and instructs it to check all 
# properties included in the file
#
# Arguments: 
#   1. Benchmark file
#   2. ByMC options
#   3. ByMC mode name
run_benchmark () {
    printf "Checking benchmark ${1} with ByMC with mode ${3}\n" | tee -a "${LOGFILE}"

    local RET=0

    # By default model checker output is written to the logfile
    local MC_OUTPUT=${LOGFILE}
    # If 3rd argument is true, set to output to stdout instead
    if [ "${LOG_TO_STDOUT}" = true ]; then 
        MC_OUTPUT="/dev/stdout"
    fi

    # Execute ByMC and save timing to 
    if [ "${GNU_TIME_FOUND}" = true ]; then
        { "${TIME_CMD}" -f "${TIMEFORMAT}" timeout "${TIMEOUT}" "${EXECUTABLE}" "${BENCHMARK_DIR}/${1}" "all" "${2}" >> "${LOGFILE}"; RET=$?; }  2> "${TMP_TIME_FILE}"
    else
        { time timeout "${TIMEOUT}" "${EXECUTABLE}" "${BENCHMARK_DIR}/${1}" "all" "${2}" >> "${LOGFILE}"; RET=$?; }  2> "${TMP_TIME_FILE}"
    fi

    if [ $RET -eq 124 ]; then
        # Timeout has occurred
        printf "TIMEOUT for ByMC on '${1}'\n" | tee -a "${LOGFILE}"
        write_bymc_bench_res "${1}" "TO" "-" "" "${3}"
    else
        if [ $RET -gt 124 ]; then 
            # An error occurred when invoking the timeout command
            printf "Failed to invoke the 'timeout' command. Timeout returned code '$RET'\n"
            exit $RET
        elif [ $RET -eq 0 ]; then
            printf "ByMC returned 0. Benchmark '${1}' is safe or a syntax error occurred\n"
            process_exec_time "${1}" "" "${3}"
        elif [ $RET -eq 1 ]; then
            printf "Benchmark '${1}' is unsafe\n"
            process_exec_time "${1}" "unsafe" "${3}"
        else 
            printf "Got unknown exit code '${RET}' from ByMC\n"
            write_bymc_bench_res "${1}" "Err" "-" "" "${3}"
        fi
    fi

    printf "\n" | tee -a "${LOGFILE}"
}

# Function to run all small BYMC benchmarks
#
# Arguments: 
#   1. ByMC options
#   2. ByMC mode name
run_small_benchmarks () {
    printf "Checking small BYMC benchmarks\n" | tee -a "${LOGFILE}"

    SMALL_BENCH_DIR="ByMC/isola18/ta-(handcoded)"

    run_benchmark "${SMALL_BENCH_DIR}/aba.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/bcrb.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/bosco.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/c1cs.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/cc.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/cf1s.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/nbacg.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/nbacr.ta" $@
    run_benchmark "${SMALL_BENCH_DIR}/strb.ta" $@

    printf "\nFinished checking small benchmarks\n\n\n" | tee -a "${LOGFILE}"
}

# Function to run all big BYMC benchmarks
#
# Arguments: 
#   1. ByMC options
#   2. ByMC mode name
run_big_benchmarks () {
    printf "Checking big (generated) BYMC benchmarks with ByMC\n" | tee -a "${LOGFILE}"

    BIG_BENCH_DIR="/ByMC"

    # Exclude benchmarks not part of the main evaluation
    if [ "${EXTENDED}" = true ]; then
        # concur14
        run_benchmark "${BIG_BENCH_DIR}/concur14/asyn-byzagreement0.ta"  $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/asyn-ray97-nbac-clean.ta"  $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/asyn-ray97-nbac.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/bcast-byz.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/bcast-folklore-crash.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/cond-consensus2.ta" $@
        run_benchmark "${BIG_BENCH_DIR}/concur14/toy.ta" $@

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
        run_benchmark "${BIG_BENCH_DIR}/cav15/promela/nbacg-asyn-guer01-nbac.ta" $@
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

    printf "\nFinished checking big benchmarks with ByMC\n\n\n" | tee -a "${LOGFILE}"
}

# Function to run all small red-belly benchmarks without resets
#
# Arguments: 
#   1. ByMC options
#   2. ByMC mode name
run_rb_wo_reset_benchmarks () {
    printf "Checking small red-belly benchmarks without resets  with ByMC\n" | tee -a "${LOGFILE}"

    RB_SMALL_BENCH_DIR="red-belly"

    run_benchmark "${RB_SMALL_BENCH_DIR}/rb-bc.ta" $@
    run_benchmark "${RB_SMALL_BENCH_DIR}/rb-simple.ta" $@
    run_benchmark "${RB_SMALL_BENCH_DIR}/rb.ta" $@

    printf "\nFinished checking small red-belly benchmarks without resets with ByMC\n\n\n" | tee -a "${LOGFILE}"
}


# Execute the smoke tests
smoke_tests () {
    printf "Executing the smoke tests

This mode will execute the 'ByMC Handcoded ISOLA18' benchmarks for ByMC. All of 
these benchmarks should be reported to be safe, and some benchmarks should 
finish within the 30s timeout set for this benchmark run by default.

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

    run_small_benchmarks "-O schema.tech=ltl" "ltl"

    printf "\nFinished executing smoke tests\n\n"
}



################################################################################
### Main functionality of the benchmarking script
################################################################################

printf "Welcome to the ByMC benchmark script written by the TACO team.

Use '--help' or '-h' to see all available options.\n\n"

while [ $# -gt 0 ]; do
  case "${1}" in
    -t|--timeout)
        TIMEOUT="${2}"
        shift # past argument
        shift # past value
        ;;
    -e|--extended)
        EXTENDED=true
        shift # past argument
        ;;
    --log-to-stdout)
        LOG_TO_STDOUT=true
        LOGFILE=/dev/null
        shift # past argument
        ;;
    -s|--smoke)
        SMOKE=true
        LOG_TO_STDOUT=true
        shift # past argument
        ;;
    -h|--help)
        printf "ByMC Benchmark Script help

This is the ByMC benchmark script designed to benchmark the ByMC model checker.
This scripts supports the following options:
    -h | --help     : Print this message
    -t | --timeout  : Override the per benchmark timeout (default: '20min')
    -s | --smoke      : Execute a small set of benchmarks for the specified model 
                        checkers (default: all) that should terminate within 5min
    -e | --extended   : Benchmark the full extended set of benchmarks (this can
                        take a lot of time!) 
    --log-to-stdout : Print the logs of the model checker to stdout instead of 
                      creating a separate log file (always enabled for smoke
                      tests)

The execution time, as well as statistics on memory usage will be printed during
the benchmark execution. The output of the model checker will be stored in the
logfile (by default named 'taco-exec.log', name can be overridden by setting the 
'LOGFILE' env variable) and will be moved to 'OUTDIR' (by default '/storage', 
can be overridden using 'OUTDIR' env variable) once the benchmark set is 
completed.
"
        exit 0
        ;;
    *)
        printf "Unrecognized option '${1}'. Use '--help' / '-h'  for available \
options.\n" 1>&2
        exit 1
        ;;
  esac
done

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
if [ $SMOKE = true ]; then 
    smoke_tests 
    exit 0
fi

# Make the user aware of extended setting
if [ "${EXTENDED}" = true ]; then
    printf "Executing the extended TACO benchmark suite. This can take a lot of 
    time!\n"
fi

printf "Benchmarking ByMC in its default mode (ltl)\n"
run_small_benchmarks "-O schema.tech=ltl" "ltl"
run_rb_wo_reset_benchmarks "-O schema.tech=ltl" "ltl"
run_big_benchmarks "-O schema.tech=ltl" "ltl"

# Exclude cav15 mode as its not part of the main evaluation
if [ "${EXTENDED}" = true ]; then
    printf "Benchmarking ByMC in cav15 mode\n"
    run_small_benchmarks "-O schema.tech=cav15" "cav15"
    run_rb_wo_reset_benchmarks "-O schema.tech=cav15" "cav15"
    run_big_benchmarks "-O schema.tech=cav15" "cav15"
fi


# Collect log file and error reports to move them to local storage 
if [ -d "${OUTDIR}" ]; then
    echo "Moving the benchmark execution log '${LOGFILE}' and counterexamples 
(which can be found in directory 'x') to local storage"
    cp --backup=t "${LOGFILE}" "${OUTDIR}"
    cp --backup=t -R ./x "${OUTDIR}"
    if [ -f "${CSV_FILE_NAME}" ]; then 
        printf "Copying the benchmark result table '${CSV_FILE_NAME}' to local \
storage\n"
        cp --backup=t "${CSV_FILE_NAME}" "${OUTDIR}"
    fi
else 
    printf "No output directory specified, or directory does not exist.
The output of ByMC has been saved to '${LOGFILE}', the benchmark table to \
'${CSV_FILE_NAME}' and you can find potential \
counter examples in the 'x' directory\n"
fi
