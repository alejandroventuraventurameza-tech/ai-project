# IE Project — integrar PDF compacto sin sobrescribir ramas ni borrar trabajo.
# PowerShell 5.1+ en Windows. Ejecutar desde cualquier directorio.
# Por defecto recompila en WSL con las figuras ORIGINALES de GitHub.
# Ejemplo:
#   powershell -ExecutionPolicy Bypass -File scripts/sync_compact_pdf.ps1
# Alternativa si WSL carece de TeX (PDF precompilado del chat, huella obligatoria):
#   powershell -ExecutionPolicy Bypass -File scripts/sync_compact_pdf.ps1 -SourcePdf "$HOME\Downloads\IE_Project_Articulo_Compacto_Candidato.pdf"
param(
  [string]$Repo = (Join-Path $HOME 'projects\IE_project\ai-project'),
  [string]$SourcePdf = '',
  [switch]$NoPush
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$branch = 'work/ie-paper-eight-results-candidate-20261125'
$expectedPrebuiltSha256 = '5672d626f3bc4a79227ede4d61b7bde1f826607699bfe8b789e7300f70747e92'
$repoRoot = [System.IO.Path]::GetFullPath($Repo)
$destPdf = Join-Path $repoRoot 'paper\paper.pdf'

function Run-Git {
  param([Parameter(ValueFromRemainingArguments=$true)][string[]]$GitArgs)
  & git @GitArgs
  if ($LASTEXITCODE -ne 0) { throw ("git {0} falló (código {1})" -f ($GitArgs -join ' '), $LASTEXITCODE) }
}
function BashQuote([string]$s) {
  return "'" + $s.Replace("'", "'\''") + "'"
}

if (!(Test-Path -LiteralPath (Join-Path $repoRoot '.git'))) {
  throw "No existe un repositorio Git en: $repoRoot"
}
if ((-not [string]::IsNullOrWhiteSpace($SourcePdf)) -and (-not (Test-Path -LiteralPath $SourcePdf))) {
  throw "PDF de origen inexistente: $SourcePdf"
}
if (!(Test-Path -LiteralPath (Join-Path $repoRoot 'paper\paper.tex'))) {
  throw "No existe paper\paper.tex en $repoRoot"
}

Push-Location $repoRoot
try {
  $remote = (& git remote get-url origin).Trim()
  if ($LASTEXITCODE -ne 0 -or $remote -notmatch 'alejandroventuraventurameza-tech/ai-project') {
    throw "La ruta remota no corresponde al repositorio IE project esperado: $remote"
  }
  $dirty = @(& git status --porcelain)
  if ($LASTEXITCODE -ne 0) { throw 'No fue posible leer git status' }
  if ($dirty.Count -gt 0) {
    throw 'El árbol tiene cambios locales. Guárdalos o crea un commit antes de usar este integrador.'
  }

  Run-Git fetch origin $branch
  & git show-ref --verify --quiet ("refs/heads/" + $branch)
  $exists = ($LASTEXITCODE -eq 0)
  if ($exists) { Run-Git switch $branch }
  else { Run-Git switch --track ("origin/" + $branch) }
  Run-Git pull --ff-only origin $branch

  $current = (& git branch --show-current).Trim()
  if ($current -ne $branch) { throw "La rama activa es $current, se esperaba $branch" }

  if ([string]::IsNullOrWhiteSpace($SourcePdf)) {
    if (!(Get-Command wsl.exe -ErrorAction SilentlyContinue)) {
      throw 'No se detecta WSL. Proporciona -SourcePdf con el PDF descargado desde el chat.'
    }
    # Convertir la ruta de Windows al punto de montaje WSL, sin inferir el nombre del usuario.
    $wslRepo = (& wsl.exe -- wslpath -a $repoRoot).Trim()
    if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($wslRepo)) {
      throw "wslpath falló al convertir $repoRoot"
    }
    $cmd = 'cd ' + (BashQuote $wslRepo) + ' && bash scripts/build_compact_paper.sh'
    Write-Host 'Compilando paper.pdf desde los archivos y figuras originales del repositorio (WSL)...'
    & wsl.exe -- bash -lc $cmd
    if ($LASTEXITCODE -ne 0) {
      throw 'Fallo de compilación local: comprueba que WSL tenga pdflatex y bibtex/bibtex8.'
    }
  } else {
    $origin = [System.IO.Path]::GetFullPath($SourcePdf)
    $actual = (Get-FileHash -LiteralPath $origin -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($actual -ne $expectedPrebuiltSha256) {
      throw "SHA-256 del PDF distinto del candidato revisado: $actual"
    }
    Copy-Item -LiteralPath $origin -Destination $destPdf -Force
    Write-Warning 'Se copió el PDF local revisado. Para correspondencia exacta con las figuras originales es preferible recompilar en WSL.'
  }

  if (!(Test-Path -LiteralPath $destPdf)) { throw 'No se produjo paper.pdf' }
  $len = (Get-Item -LiteralPath $destPdf).Length
  if ($len -lt 100000) { throw "PDF inusualmente pequeño ($len bytes), se interrumpe." }
  $pdfHash = (Get-FileHash -LiteralPath $destPdf -Algorithm SHA256).Hash.ToLowerInvariant()
  Write-Host "SHA-256 del PDF a integrar: $pdfHash"
  Write-Host "Tamaño: $len bytes"

  $otherChanges = @(& git status --porcelain | Where-Object {
    ($_ -notmatch 'paper/paper\.pdf$') -and ($_ -notmatch 'paper\\paper\.pdf$')
  })
  if ($otherChanges.Count -gt 0) {
    throw ('La compilación modificó otros archivos; no se mezclará con el PDF: ' + ($otherChanges -join '; '))
  }

  Run-Git add -- paper/paper.pdf
  & git diff --cached --quiet -- paper/paper.pdf
  $diffCode = $LASTEXITCODE
  if ($diffCode -eq 0) {
    Write-Host 'paper/paper.pdf ya coincide con lo registrado en la rama.'
    return
  }
  if ($diffCode -ne 1) { throw "Fallo al comparar el archivo PDF, código $diffCode" }

  Run-Git commit -m 'build(paper): synchronize compact PDF with eight-result source'
  $sha = (& git rev-parse HEAD).Trim()
  Write-Host "Commit generado: $sha"
  if ($NoPush) {
    Write-Host 'NoPush activo. El commit permanece solo en este equipo.'
  } else {
    Run-Git push origin $branch
    Write-Host "PDF publicado en PR #4: https://github.com/alejandroventuraventurameza-tech/ai-project/pull/4"
    Write-Host 'Revisar build y código antes de fusionar. No se ha tocado main.'
  }
} finally {
  Pop-Location
}
