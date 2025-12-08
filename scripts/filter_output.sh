#!/bin/bash
# Função auxiliar para filtrar saída do OpenJML
# Uso: filter_output <nome_da_classe>
# Exemplo: filter_output "Bishop"

CLASS_NAME="$1"

if [ -z "$CLASS_NAME" ]; then
    echo "Erro: Nome da classe não fornecido"
    exit 1
fi

# Filtra apenas linhas relacionadas à classe específica
grep --line-buffered -E "($CLASS_NAME\.java|verify:|error:|warning:)" | \
    grep -E "($CLASS_NAME\.java|verify:|error:|warning:)" | \
    sed 's/^/  /'

