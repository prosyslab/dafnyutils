export DOTNET_ROOT="${DOTNET_ROOT:-/usr/share/dotnet}"
default_nuget_packages="${HOME:-/root}/.nuget/packages"
export NUGET_PACKAGES="${NUGET_PACKAGES:-$default_nuget_packages}"
export DOTNET_CLI_USE_MSBUILD_SERVER="${DOTNET_CLI_USE_MSBUILD_SERVER:-0}"
export MSBUILDDISABLENODEREUSE="${MSBUILDDISABLENODEREUSE:-1}"
export UseSharedCompilation="${UseSharedCompilation:-false}"
export RestoreSources="${RestoreSources:-$NUGET_PACKAGES}"
export RestoreIgnoreFailedSources="${RestoreIgnoreFailedSources:-true}"

DOTNET_GCHeapHardLimit="${DOTNET_GCHeapHardLimit:-@{DOTNET_HEAP_LIMIT}}"
COMPlus_GCHeapHardLimit="${COMPlus_GCHeapHardLimit:-$DOTNET_GCHeapHardLimit}"
export DOTNET_GCHeapHardLimit COMPlus_GCHeapHardLimit
