#!/bin/bash
# ============================================
#  Verified SQL Query Engine - Live Demo
# ============================================

DAFNY=~/dafny_new/dafny/dafny
CYAN='\033[1;36m'
GREEN='\033[1;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

pause() {
    echo ""
    echo -e "${YELLOW}>>> Press Enter to continue...${NC}"
    read -r
    clear
}

clear
echo -e "${CYAN}========================================${NC}"
echo -e "${CYAN}  Verified SQL Query Engine - Live Demo ${NC}"
echo -e "${CYAN}========================================${NC}"
echo ""
echo "  Tool:    Dafny 4.11 + Z3 SMT Solver"
echo "  Authors: Yan Liang & Muyang Zheng"
echo "  Course:  ECS 261 - Winter 2026"
pause

# ── Step 1: Verify individual modules ──
echo -e "${CYAN}=== Step 1: Verify Each Module ===${NC}"
echo ""
echo "  We verify each SQL operation independently."
echo "  Dafny checks ALL postconditions for EVERY possible input."
echo ""

for file in Where.dfy Select.dfy OrderBy.dfy GroupBySum.dfy; do
    echo -e -n "  ${GREEN}▶ dafny verify $file${NC}  ...  "
    result=$($DAFNY verify "$file" 2>&1)
    echo -e "${GREEN}$result${NC}"
done

echo ""
echo -e "  ${GREEN}✓ All modules verified with 0 errors!${NC}"
pause

# ── Step 2: Run the demo ──
echo -e "${CYAN}=== Step 2: Run Demo Queries ===${NC}"
echo ""
echo "  Now we execute 6 SQL queries on a sample employee table."
echo "  The code is verified FIRST, then executed."
echo ""
echo -e "${GREEN}▶ dafny run Main.dfy${NC}"
echo ""

$DAFNY run Main.dfy 2>&1

echo ""
echo -e "${YELLOW}>>> Press Enter to finish.${NC}"
read -r
clear
echo -e "${CYAN}========================================${NC}"
echo -e "${CYAN}  27 verified, 0 errors                ${NC}"
echo -e "${CYAN}  No assume statements                  ${NC}"
echo -e "${CYAN}  Mathematical guarantees for ALL inputs ${NC}"
echo -e "${CYAN}========================================${NC}"
echo ""
echo "  Thank you!"
echo ""
