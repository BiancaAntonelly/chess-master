#!/bin/bash
# Funções auxiliares comuns para os scripts de verificação

# Função para mostrar progresso visual
show_progress() {
    local step=$1
    local total=$2
    local message=$3
    echo "[$step/$total] $message"
}

# Função para mostrar estatísticas
show_stats() {
    local class_name=$1
    local log_file="/tmp/jml_output_${class_name}.log"
    
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "📈 Estatísticas:"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    # Conta erros e avisos
    local errors=$(grep -c "error:" "$log_file" 2>/dev/null || echo "0")
    local warnings=$(grep -c "warning:" "$log_file" 2>/dev/null || echo "0")
    local verify_issues=$(grep -c "verify:" "$log_file" 2>/dev/null || echo "0")
    
    echo "  🔴 Erros:     $errors"
    echo "  🟡 Avisos:    $warnings"
    echo "  🔵 Verificações: $verify_issues"
    echo ""
    
    if [ "$errors" -eq "0" ] && [ "$verify_issues" -eq "0" ]; then
        echo "✨ ${class_name}.java: VERIFICAÇÃO BEM-SUCEDIDA!"
        return 0
    else
        echo "⚠️  ${class_name}.java: Encontrados problemas (veja acima)"
        return 1
    fi
}

# Função para mostrar cabeçalho
show_header() {
    local class_name=$1
    echo "=========================================="
    echo "🔍 Verificando ${class_name}.java"
    echo "=========================================="
    echo ""
}

# Função para mostrar rodapé
show_footer() {
    local class_name=$1
    echo ""
    echo "=========================================="
    echo "🏁 Fim da verificação de ${class_name}.java"
    echo "=========================================="
    echo ""
}

