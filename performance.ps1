$outputFile = "performance.txt"

function ExecuteTestCase($inputFile) {
    $proc = Start-Process -FilePath "python" -ArgumentList ".\solvepy3.py", $inputFile -NoNewWindow -PassThru

    # 90초 경과 시간을 계산하기 위한 시작 시간 저장
    $startTime = Get-Date

    # wait up to 90 seconds for normal termination
    $proc | Wait-Process -Timeout 90 -ErrorAction SilentlyContinue -ErrorVariable timeouted

    if ($timeouted) {
        # terminate the process if it exceeded the timeout
        $proc | Stop-Process -Force
        return "timeout"
    }
    else {
        # calculate the execution time in seconds
        $totalSeconds = (Get-Date) - $startTime | Select-Object -ExpandProperty TotalSeconds
        return $totalSeconds
    }
}

# uf20-01.cnf ~ uf20-09.cnf
Write-Output "Running uf20-01.cnf to uf20-09.cnf..."
for ($i = 1; $i -le 9; $i++) {
    $inputFile = ".\examples\uf20-91\uf20-$(("{0:D2}" -f $i)).cnf"
    $result = ExecuteTestCase $inputFile

    if ($result -eq "timeout") {
        Write-Output "uf20-$(("{0:D2}" -f $i)): timeout" | Out-File -FilePath $outputFile -Append
    }
    else {
        Write-Output "uf20-$(("{0:D2}" -f $i)): $($result) seconds" | Out-File -FilePath $outputFile -Append
    }
}

# uf100-01.cnf ~ uf100-09.cnf
Write-Output "Running uf100-01.cnf to uf100-09.cnf..."
for ($i = 1; $i -le 9; $i++) {
    $inputFile = ".\examples\uf100-430\uf100-$(("{0:D2}" -f $i)).cnf"
    $result = ExecuteTestCase $inputFile

    if ($result -eq "timeout") {
        Write-Output "uf100-$(("{0:D2}" -f $i)): timeout" | Out-File -FilePath $outputFile -Append
    }
    else {
        Write-Output "uf100-$(("{0:D2}" -f $i)): $($result) seconds" | Out-File -FilePath $outputFile -Append
    }
}

# uf125-01.cnf ~ uf125-09.cnf
Write-Output "Running uf125-01.cnf to uf125-09.cnf..."
for ($i = 1; $i -le 9; $i++) {
    $inputFile = ".\examples\UF125.538.100\uf125-$(("{0:D2}" -f $i)).cnf"
    $result = ExecuteTestCase $inputFile

    if ($result -eq "timeout") {
        Write-Output "uf125-$(("{0:D2}" -f $i)): timeout" | Out-File -FilePath $outputFile -Append
    }
    else {
        Write-Output "uf125-$(("{0:D2}" -f $i)): $($result) seconds" | Out-File -FilePath $outputFile -Append
    }
}
