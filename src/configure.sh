echo "# compilation options" > _CoqProject
echo "-R NormTypes NormTypes" >> _CoqProject
echo "-arg -allow-sprop" >> _CoqProject
echo "" >> _CoqProject
echo "# Coq Files" >> _CoqProject

# ajouter des grep -v si on veut exclure certains fichiers de la
# compilation par défaut.
find . -name "*.v" >> _CoqProject


coq_makefile -f _CoqProject -o Makefile

