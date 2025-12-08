#!/bin/bash
# Template para scripts de verificação
# Substitua CLASS_NAME e adicione os arquivos de dependência

CLASS_NAME="CLASS_NAME_HERE"
show_header "$CLASS_NAME"

# Contador de progresso
STEP=1
TOTAL_STEPS=3

show_progress $STEP $TOTAL_STEPS "📦 Carregando dependências..."
STEP=$((STEP + 1))

show_progress $STEP $TOTAL_STEPS "⚙️  Executando OpenJML..."
STEP=$((STEP + 1))

# Executa OpenJML e mostra progresso
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Resultados da Verificação:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

openjml --esc --progress -classpath src/main/java \
    DEPENDENCIES_HERE \
    2>&1 | \
    tee /tmp/jml_output_${CLASS_NAME}.log | \
    grep --line-buffered -E "(${CLASS_NAME}\.java|verify:|error:|warning:)" | \
    grep -E "(${CLASS_NAME}\.java|verify:|error:|warning:)" | \
    sed 's/^/  │ /' || true

echo ""
show_progress $STEP $TOTAL_STEPS "✅ Verificação concluída!"

show_stats "$CLASS_NAME"
show_footer "$CLASS_NAME"

