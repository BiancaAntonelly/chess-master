package chess.pieces;

import boardgame.Board;
import boardgame.Position;
import chess.ChessMatch;
import chess.ChessPiece;
import chess.Color;

/**
 * Classe que representa um Rei no jogo de xadrez.
 * O rei move-se uma casa em qualquer direção (horizontal, vertical ou diagonal).
 * Também pode realizar o movimento especial de roque (castling) sob certas condições.
 */
public class King extends ChessPiece {

    //@ public invariant match != null;

    //@ spec_public
    private final /*@ non_null @*/ ChessMatch match;

    /*@ public normal_behavior
      @   requires board != null;
      @   requires color != null;
      @   requires match != null;
      @   ensures getColor() == color;
      @   ensures getMoveCount() == 0;
      @   ensures getBoard() == board;
      @   ensures this.match == match;
      @   assignable this.color, this.moveCount, this.match;
      @*/
    public King(/*@ non_null @*/ Board board,
            /*@ non_null @*/ Color color,
            /*@ non_null @*/ ChessMatch match) {
        super(board, color);
        this.match = match;
    }

    /*@ private normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   requires getBoard().positionExists(position);
      @   ensures \result == true ==> (getBoard().piece(position) == null ||
      @           ((ChessPiece)getBoard().piece(position)).getColor() != getColor());
      @   ensures \result == false ==> (getBoard().piece(position) != null &&
      @           ((ChessPiece)getBoard().piece(position)).getColor() == getColor());
      @   assignable \nothing;
      @   pure
      @*/
    private /*@ pure @*/ boolean canMove(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p == null || p.getColor() != getColor();
    }

    /*@ private normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @   requires getBoard().positionExists(position);
      @   ensures \result == true ==> (getBoard().piece(position) instanceof Rook &&
      @           ((ChessPiece)getBoard().piece(position)).getColor() == getColor() &&
      @           ((ChessPiece)getBoard().piece(position)).getMoveCount() == 0);
      @   ensures \result == false ==> (!(getBoard().piece(position) instanceof Rook) ||
      @           ((ChessPiece)getBoard().piece(position)).getColor() != getColor() ||
      @           ((ChessPiece)getBoard().piece(position)).getMoveCount() != 0);
      @   assignable \nothing;
      @   pure
      @*/
    private /*@ pure @*/ boolean testRookCastling(/*@ non_null @*/ Position position) {
        ChessPiece p = (ChessPiece) getBoard().piece(position);
        return p instanceof Rook && p.getColor() == getColor() && p.getMoveCount() == 0;
    }

    /*@ also
      @ public normal_behavior
      @   requires position != null;
      @   requires position.getRow() >= 0 && position.getRow() < 8;
      @   requires position.getCol() >= 0 && position.getCol() < 8;
      @
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @
      @   // A posição atual do rei não é um movimento válido
      @   ensures !\result[position.getRow()][position.getCol()];
      @
      @   // Movimentos normais: máximo de 1 casa de distância (exceto roque)
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c] &&
      @               !(r == position.getRow() &&
      @                 java.lang.Math.abs(c - position.getCol()) == 2);
      @               java.lang.Math.abs(r - position.getRow()) <= 1 &&
      @               java.lang.Math.abs(c - position.getCol()) <= 1);
      @
      @   // Roque: se houver movimento de 2 casas horizontalmente, é roque
      @   ensures (\forall int r, c;
      @               0 <= r && r < 8 && 0 <= c && c < 8 && \result[r][c] &&
      @               java.lang.Math.abs(c - position.getCol()) == 2;
      @               r == position.getRow());
      @
      @   // Movimento para cima (norte)
      @   ensures position.getRow() > 0 &&
      @           canMove(new Position(position.getRow() - 1, position.getCol()))
      @               ==> \result[position.getRow() - 1][position.getCol()];
      @
      @   // Movimento para baixo (sul)
      @   ensures position.getRow() < 7 &&
      @           canMove(new Position(position.getRow() + 1, position.getCol()))
      @               ==> \result[position.getRow() + 1][position.getCol()];
      @
      @   // Movimento para esquerda (oeste)
      @   ensures position.getCol() > 0 &&
      @           canMove(new Position(position.getRow(), position.getCol() - 1))
      @               ==> \result[position.getRow()][position.getCol() - 1];
      @
      @   // Movimento para direita (leste)
      @   ensures position.getCol() < 7 &&
      @           canMove(new Position(position.getRow(), position.getCol() + 1))
      @               ==> \result[position.getRow()][position.getCol() + 1];
      @
      @   // Movimento diagonal noroeste
      @   ensures position.getRow() > 0 && position.getCol() > 0 &&
      @           canMove(new Position(position.getRow() - 1, position.getCol() - 1))
      @               ==> \result[position.getRow() - 1][position.getCol() - 1];
      @
      @   // Movimento diagonal nordeste
      @   ensures position.getRow() > 0 && position.getCol() < 7 &&
      @           canMove(new Position(position.getRow() - 1, position.getCol() + 1))
      @               ==> \result[position.getRow() - 1][position.getCol() + 1];
      @
      @   // Movimento diagonal sudoeste
      @   ensures position.getRow() < 7 && position.getCol() > 0 &&
      @           canMove(new Position(position.getRow() + 1, position.getCol() - 1))
      @               ==> \result[position.getRow() + 1][position.getCol() - 1];
      @
      @   // Movimento diagonal sudeste
      @   ensures position.getRow() < 7 && position.getCol() < 7 &&
      @           canMove(new Position(position.getRow() + 1, position.getCol() + 1))
      @               ==> \result[position.getRow() + 1][position.getCol() + 1];
      @
      @   assignable \nothing;
      @*/
    @Override
    public boolean[][] possibleMoves() {

        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getCols()];

        Position p = new Position(0, 0);

        // Acima (Norte)
        p.setValues(position.getRow() - 1, position.getCol());
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Abaixo (Sul)
        p.setValues(position.getRow() + 1, position.getCol());
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Esquerda (Oeste)
        p.setValues(position.getRow(), position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Direita (Leste)
        p.setValues(position.getRow(), position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Noroeste
        p.setValues(position.getRow() - 1, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Nordeste
        p.setValues(position.getRow() - 1, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudoeste
        p.setValues(position.getRow() + 1, position.getCol() - 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Sudeste
        p.setValues(position.getRow() + 1, position.getCol() + 1);
        if (getBoard().positionExists(p) && canMove(p)) {
            mat[p.getRow()][p.getCol()] = true;
        }

        // Roque (castling)
        if (getMoveCount() == 0 && !match.getCheck()) {
            // Roque menor (kingside)
            Position posT1 = new Position(position.getRow(), position.getCol() + 3);
            if (getBoard().positionExists(posT1) && testRookCastling(posT1)) {
                Position p1 = new Position(position.getRow(), position.getCol() + 1);
                Position p2 = new Position(position.getRow(), position.getCol() + 2);
                if (getBoard().positionExists(p1) && getBoard().positionExists(p2) &&
                        getBoard().piece(p1) == null && getBoard().piece(p2) == null) {
                    mat[position.getRow()][position.getCol() + 2] = true;
                }
            }

            // Roque maior (queenside)
            Position posT2 = new Position(position.getRow(), position.getCol() - 4);
            if (getBoard().positionExists(posT2) && testRookCastling(posT2)) {
                Position p1 = new Position(position.getRow(), position.getCol() - 1);
                Position p2 = new Position(position.getRow(), position.getCol() - 2);
                Position p3 = new Position(position.getRow(), position.getCol() - 3);
                if (getBoard().positionExists(p1) && getBoard().positionExists(p2) &&
                        getBoard().positionExists(p3) &&
                        getBoard().piece(p1) == null &&
                        getBoard().piece(p2) == null &&
                        getBoard().piece(p3) == null) {
                    mat[position.getRow()][position.getCol() - 2] = true;
                }
            }
        }

        return mat;
    }

    /*@ also
      @ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.equals("K");
      @   assignable \nothing;
      @   pure
      @*/
    @Override
    public /*@ pure non_null @*/ String toString() {
        return "K";
    }
}
