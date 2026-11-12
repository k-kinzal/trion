# A prover that leaves every query open.
while read -r line; do
    case "$line" in "(check-sat)") echo unknown ;; esac
done
