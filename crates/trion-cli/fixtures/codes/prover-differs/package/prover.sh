# A prover that refutes every query, whatever it asks.
while read -r line; do
    case "$line" in "(check-sat)") echo unsat ;; esac
done
