import sys
import os
import csv
import json
import uuid
import math
import base64
import hashlib
import sqlite3
from datetime import datetime
from PySide6.QtCore import Qt, QTimer, QRectF, QPointF, QMimeData, QByteArray
from PySide6.QtGui import (
    QPen, QBrush, QColor, QPainter, QFont, QPainterPath,
    QLinearGradient, QRadialGradient, QDrag, QPixmap, QUndoStack, QUndoCommand,
    QKeySequence, QAction, QImage, QPdfWriter, QPageSize, QPageLayout
)
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QFrame, QGraphicsView, QGraphicsScene,
    QGraphicsItem, QGraphicsEllipseItem, QInputDialog, QFileDialog,
    QDialog, QFormLayout, QLineEdit, QDoubleSpinBox, QDialogButtonBox,
    QListWidget, QListWidgetItem, QAbstractItemView, QComboBox, QMessageBox,
    QSlider, QMenu
)

GRID_SIZE = 30
MIME_TYPE = "application/x-scada-component"
DB_PATH = "scada_users.db"
PROJECT_FILTER = "SCADA Project Files (*.scada *.json);;All Files (*)"


def snap_to_grid(pt: QPointF) -> QPointF:
    return QPointF(
        round(pt.x() / GRID_SIZE) * GRID_SIZE,
        round(pt.y() / GRID_SIZE) * GRID_SIZE
    )


def build_smooth_orthogonal_path(points: list[QPointF], corner_radius: float = 10.0) -> QPainterPath:
    """Converts raw waypoints into a clean 90-degree orthogonal path with smooth rounded corners."""
    path = QPainterPath()
    if not points:
        return path

    ortho = [points[0]]
    for i in range(1, len(points)):
        prev = ortho[-1]
        curr = points[i]
        if abs(curr.x() - prev.x()) > 1 and abs(curr.y() - prev.y()) > 1:
            mid_x = snap_to_grid(QPointF((prev.x() + curr.x()) / 2.0, prev.y())).x()
            if abs(mid_x - prev.x()) > 1 and abs(mid_x - curr.x()) > 1:
                ortho.append(QPointF(mid_x, prev.y()))
                ortho.append(QPointF(mid_x, curr.y()))
            else:
                ortho.append(QPointF(curr.x(), prev.y()))
        ortho.append(curr)

    cleaned = [ortho[0]]
    for pt in ortho[1:]:
        if (pt - cleaned[-1]).manhattanLength() > 1.0:
            cleaned.append(pt)

    path.moveTo(cleaned[0])
    if len(cleaned) == 2:
        path.lineTo(cleaned[1])
        return path

    for i in range(1, len(cleaned) - 1):
        p_prev = cleaned[i - 1]
        p_curr = cleaned[i]
        p_next = cleaned[i + 1]

        v1 = p_prev - p_curr
        v2 = p_next - p_curr
        len1 = math.hypot(v1.x(), v1.y())
        len2 = math.hypot(v2.x(), v2.y())

        r = min(corner_radius, len1 * 0.4, len2 * 0.4)
        if r > 1.0:
            start_arc = p_curr + QPointF((v1.x() / len1) * r, (v1.y() / len1) * r)
            end_arc = p_curr + QPointF((v2.x() / len2) * r, (v2.y() / len2) * r)
            path.lineTo(start_arc)
            path.quadTo(p_curr, end_arc)
        else:
            path.lineTo(p_curr)

    path.lineTo(cleaned[-1])
    return path


# ==============================================================================
# AUTHENTICATION DATABASE & LOGIN DIALOG
# ==============================================================================

class AuthManager:
    def __init__(self, db_path=DB_PATH):
        self.db_path = db_path
        self._init_db()

    @staticmethod
    def _hash_pw(password: str) -> str:
        return hashlib.sha256(password.encode("utf-8")).hexdigest()

    def _init_db(self):
        conn = sqlite3.connect(self.db_path)
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS users (
                username TEXT PRIMARY KEY,
                password_hash TEXT NOT NULL,
                role TEXT NOT NULL
            )
        """)
        defaults = [
            ("admin", self._hash_pw("admin123"), "Admin"),
            ("operator", self._hash_pw("op123"), "Operator"),
            ("viewer", self._hash_pw("view123"), "Viewer"),
        ]
        for u, pw, r in defaults:
            cur.execute("INSERT OR IGNORE INTO users (username, password_hash, role) VALUES (?, ?, ?)", (u, pw, r))
        conn.commit()
        conn.close()

    def authenticate(self, username: str, password: str):
        conn = sqlite3.connect(self.db_path)
        cur = conn.cursor()
        cur.execute("SELECT role FROM users WHERE username = ? AND password_hash = ?", (username, self._hash_pw(password)))
        row = cur.fetchone()
        conn.close()
        return row[0] if row else None


class LoginDialog(QDialog):
    def __init__(self, auth_manager: AuthManager, parent=None):
        super().__init__(parent)
        self.auth = auth_manager
        self.authenticated_user = None
        self.authenticated_role = None

        self.setWindowTitle("SCADA System Authentication")
        self.setFixedSize(380, 260)
        self.setStyleSheet("""
            QDialog { background-color: #0f172a; color: #f8fafc; }
            QLabel { color: #cbd5e1; font-size: 12px; }
            QLineEdit {
                background-color: #1e293b; color: #f8fafc;
                border: 1px solid #475569; border-radius: 5px;
                padding: 8px; font-size: 13px;
            }
            QLineEdit:focus { border-color: #38bdf8; }
            QPushButton {
                background-color: #0284c7; color: #ffffff;
                border: none; border-radius: 5px;
                padding: 9px; font-weight: bold; font-size: 13px;
            }
            QPushButton:hover { background-color: #0369a1; }
        """)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(28, 24, 28, 24)
        layout.setSpacing(12)

        title = QLabel("WATER DISTRIBUTION SCADA")
        title.setAlignment(Qt.AlignCenter)
        title.setStyleSheet("font-size: 16px; font-weight: bold; color: #38bdf8; letter-spacing: 1px;")
        layout.addWidget(title)

        sub = QLabel("Sign in to access HMI & CAD Workstation")
        sub.setAlignment(Qt.AlignCenter)
        sub.setStyleSheet("color: #94a3b8; font-size: 11px; margin-bottom: 6px;")
        layout.addWidget(sub)

        self.user_input = QLineEdit()
        self.user_input.setPlaceholderText("Username (admin / operator / viewer)")
        self.user_input.setText("admin")
        layout.addWidget(self.user_input)

        self.pass_input = QLineEdit()
        self.pass_input.setPlaceholderText("Password")
        self.pass_input.setEchoMode(QLineEdit.Password)
        self.pass_input.setText("admin123")
        self.pass_input.returnPressed.connect(self._attempt_login)
        layout.addWidget(self.pass_input)

        self.err_lbl = QLabel("")
        self.err_lbl.setStyleSheet("color: #f87171; font-size: 11px;")
        self.err_lbl.setAlignment(Qt.AlignCenter)
        layout.addWidget(self.err_lbl)

        login_btn = QPushButton("LOGIN TO WORKSTATION")
        login_btn.setCursor(Qt.PointingHandCursor)
        login_btn.clicked.connect(self._attempt_login)
        layout.addWidget(login_btn)

    def _attempt_login(self):
        user = self.user_input.text().strip()
        pw = self.pass_input.text()
        role = self.auth.authenticate(user, pw)
        if role:
            self.authenticated_user = user
            self.authenticated_role = role
            self.accept()
        else:
            self.err_lbl.setText("Invalid username or password.")


# ==============================================================================
# CUSTOM SYMBOL IMPORT DIALOG
# ==============================================================================

class CustomSymbolDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Import Custom P&ID / SCADA Symbol")
        self.setFixedWidth(420)
        self.setStyleSheet("background-color: #121722; color: #e2e8f0;")
        self.file_path = ""

        layout = QFormLayout(self)

        self.name_edit = QLineEdit("Custom Unit")
        self.name_edit.setStyleSheet("background: #1e293b; padding: 6px; border: 1px solid #475569;")
        layout.addRow("Symbol Name:", self.name_edit)

        self.behavior_combo = QComboBox()
        self.behavior_combo.addItems([
            "Pass-Through / Valve (Click Toggle)",
            "Pump / Booster (Active Flow)",
            "Storage Tank / Vessel",
            "Water Source (Inflow)",
            "Demand Sink (Outflow)"
        ])
        self.behavior_combo.setStyleSheet("background: #1e293b; padding: 6px; border: 1px solid #475569;")
        layout.addRow("Hydraulic Behavior:", self.behavior_combo)

        file_row = QHBoxLayout()
        self.path_lbl = QLineEdit()
        self.path_lbl.setReadOnly(True)
        self.path_lbl.setPlaceholderText("Select .svg or .png file...")
        self.path_lbl.setStyleSheet("background: #1e293b; padding: 6px; border: 1px solid #475569;")
        browse_btn = QPushButton("Browse...")
        browse_btn.setStyleSheet("background: #0284c7; padding: 6px 12px; font-weight: bold;")
        browse_btn.clicked.connect(self._browse_file)
        file_row.addWidget(self.path_lbl)
        file_row.addWidget(browse_btn)
        layout.addRow("Symbol Graphic:", file_row)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self._validate_accept)
        buttons.rejected.connect(self.reject)
        layout.addRow(buttons)

    def _browse_file(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Select Custom Symbol Image", "", "Vector & Images (*.svg *.png *.jpg)"
        )
        if path:
            self.file_path = path
            self.path_lbl.setText(os.path.basename(path))
            if self.name_edit.text() == "Custom Unit":
                self.name_edit.setText(os.path.splitext(os.path.basename(path))[0].replace("_", " ").title())

    def _validate_accept(self):
        if not self.file_path or not os.path.exists(self.file_path):
            QMessageBox.warning(self, "Missing File", "Please select a valid SVG or PNG file.")
            return
        self.accept()

    def get_symbol_spec(self):
        behavior_map = {0: "valve", 1: "motor", 2: "tank", 3: "source", 4: "demand"}
        with open(self.file_path, "rb") as f:
            raw_bytes = f.read()
        b64_data = base64.b64encode(raw_bytes).decode("ascii")
        ext = os.path.splitext(self.file_path)[1].lower()
        return {
            "symbol_id": f"custom_{str(uuid.uuid4())[:6]}",
            "name": self.name_edit.text().strip() or "Custom Symbol",
            "behavior": behavior_map[self.behavior_combo.currentIndex()],
            "ext": ext,
            "b64_data": b64_data
        }


# ==============================================================================
# UNDO / REDO COMMANDS
# ==============================================================================

class AddNodeCommand(QUndoCommand):
    def __init__(self, scene, node):
        super().__init__(f"Add {node.label}")
        self.scene = scene
        self.node = node

    def redo(self):
        if self.node.scene() != self.scene:
            self.scene.addItem(self.node)

    def undo(self):
        if self.node.scene() == self.scene:
            self.scene.removeItem(self.node)


class MoveNodeCommand(QUndoCommand):
    def __init__(self, node, old_pos: QPointF, new_pos: QPointF):
        super().__init__(f"Move {node.label}")
        self.node = node
        self.old_pos = QPointF(old_pos)
        self.new_pos = QPointF(new_pos)

    def redo(self):
        self.node.setPos(self.new_pos)
        for p in self.node.connected_pipes:
            p.rebuild_path()

    def undo(self):
        self.node.setPos(self.old_pos)
        for p in self.node.connected_pipes:
            p.rebuild_path()


class AddPipeCommand(QUndoCommand):
    def __init__(self, scene, pipe):
        super().__init__(f"Connect {pipe.src_node.label} to {pipe.dst_node.label}")
        self.scene = scene
        self.pipe = pipe

    def redo(self):
        if self.pipe not in self.pipe.src_node.connected_pipes:
            self.pipe.src_node.connected_pipes.append(self.pipe)
        if self.pipe not in self.pipe.dst_node.connected_pipes:
            self.pipe.dst_node.connected_pipes.append(self.pipe)
        if self.pipe.scene() != self.scene:
            self.scene.addItem(self.pipe)
        self.pipe.rebuild_path()

    def undo(self):
        self.pipe.hide_handles()
        if self.pipe in self.pipe.src_node.connected_pipes:
            self.pipe.src_node.connected_pipes.remove(self.pipe)
        if self.pipe in self.pipe.dst_node.connected_pipes:
            self.pipe.dst_node.connected_pipes.remove(self.pipe)
        if self.pipe.scene() == self.scene:
            self.scene.removeItem(self.pipe)


class DeleteItemsCommand(QUndoCommand):
    def __init__(self, scene, nodes, pipes):
        super().__init__("Delete Selection")
        self.scene = scene
        self.nodes = list(nodes)
        pipe_set = set(pipes)
        for n in self.nodes:
            for p in n.connected_pipes:
                pipe_set.add(p)
        self.pipes = list(pipe_set)

    def redo(self):
        for p in self.pipes:
            p.hide_handles()
            if p in p.src_node.connected_pipes:
                p.src_node.connected_pipes.remove(p)
            if p in p.dst_node.connected_pipes:
                p.dst_node.connected_pipes.remove(p)
            if p.scene() == self.scene:
                self.scene.removeItem(p)
        for n in self.nodes:
            if n.scene() == self.scene:
                self.scene.removeItem(n)

    def undo(self):
        for n in self.nodes:
            if n.scene() != self.scene:
                self.scene.addItem(n)
        for p in self.pipes:
            if p not in p.src_node.connected_pipes:
                p.src_node.connected_pipes.append(p)
            if p not in p.dst_node.connected_pipes:
                p.dst_node.connected_pipes.append(p)
            if p.scene() != self.scene:
                self.scene.addItem(p)
            p.rebuild_path()


# ==============================================================================
# PROPERTY EDITOR DIALOG
# ==============================================================================

class PropertyDialog(QDialog):
    def __init__(self, node_item, parent=None):
        super().__init__(parent)
        self.setWindowTitle(f"Configure {node_item.label}")
        self.setStyleSheet("background-color: #121722; color: #e2e8f0;")
        self.node = node_item

        layout = QFormLayout(self)
        self.name_edit = QLineEdit(self.node.label)
        self.name_edit.setStyleSheet("background: #1e293b; padding: 5px; border: 1px solid #475569;")
        layout.addRow("Tag / Name:", self.name_edit)

        self.cap_spin = None
        self.vol_spin = None
        self.flow_spin = None

        if self.node.node_type == "tank":
            self.cap_spin = QDoubleSpinBox()
            self.cap_spin.setRange(1.0, 10000.0)
            self.cap_spin.setValue(self.node.capacity)
            self.cap_spin.setSuffix(" m³")
            self.cap_spin.setStyleSheet("background: #1e293b; padding: 4px;")
            layout.addRow("Tank Capacity:", self.cap_spin)

            self.vol_spin = QDoubleSpinBox()
            self.vol_spin.setRange(0.0, 10000.0)
            self.vol_spin.setValue(self.node.volume)
            self.vol_spin.setSuffix(" m³")
            self.vol_spin.setStyleSheet("background: #1e293b; padding: 4px;")
            layout.addRow("Initial Volume:", self.vol_spin)

        if self.node.node_type in ("source", "motor", "demand"):
            self.flow_spin = QDoubleSpinBox()
            self.flow_spin.setRange(0.5, 2000.0)
            self.flow_spin.setValue(self.node.rated_flow)
            self.flow_spin.setSuffix(" m³/h")
            self.flow_spin.setStyleSheet("background: #1e293b; padding: 4px;")
            lbl = "Peak Demand:" if self.node.node_type == "demand" else "Rated Capacity:"
            layout.addRow(lbl, self.flow_spin)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addRow(buttons)

    def apply_changes(self):
        self.node.label = self.name_edit.text().strip() or self.node.label
        if self.cap_spin:
            self.node.capacity = self.cap_spin.value()
        if self.vol_spin:
            self.node.volume = min(self.node.capacity, self.vol_spin.value())
        if self.flow_spin:
            self.node.rated_flow = self.flow_spin.value()
        self.node.update()


# ==============================================================================
# INTERACTIVE PIPE VERTEX HANDLE & SMOOTH ORTHOGONAL PIPE ITEM
# ==============================================================================

class PipeVertexHandle(QGraphicsEllipseItem):
    def __init__(self, pipe_item, index: int, pt: QPointF):
        super().__init__(-5, -5, 10, 10)
        self.pipe_item = pipe_item
        self.index = index
        self.setPos(pt)
        self.setBrush(QBrush(QColor("#38bdf8")))
        self.setPen(QPen(QColor("#0f172a"), 1.5))
        self.setZValue(10)
        self.setFlags(
            QGraphicsItem.ItemIsMovable |
            QGraphicsItem.ItemSendsGeometryChanges
        )
        self.setCursor(Qt.SizeAllCursor)

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemPositionChange:
            snapped = snap_to_grid(value)
            if 0 <= self.index < len(self.pipe_item.waypoints):
                self.pipe_item.waypoints[self.index] = snapped
                self.pipe_item.rebuild_path()
            return snapped
        return super().itemChange(change, value)

    def mousePressEvent(self, event):
        if event.button() == Qt.RightButton:
            self.pipe_item.remove_waypoint(self.index)
            event.accept()
            return
        super().mousePressEvent(event)


class PipeEdgeItem(QGraphicsItem):
    def __init__(self, pipe_id, src_node, dst_node, waypoints=None, diameter_mm=75, color="#06b6d4"):
        super().__init__()
        self.setZValue(-1)
        self.setFlag(QGraphicsItem.ItemIsSelectable, True)
        self.pipe_id = pipe_id
        self.src_node = src_node
        self.dst_node = dst_node
        self.waypoints = [snap_to_grid(QPointF(x, y)) for x, y in (waypoints or [])]
        self.diameter_mm = diameter_mm
        self.flow_color = QColor(color)

        self.current_flow = 0.0
        self.dash_offset = 0.0
        self.path = QPainterPath()
        self.handles = []

        self.src_node.connected_pipes.append(self)
        self.dst_node.connected_pipes.append(self)
        self.rebuild_path()

    def rebuild_path(self):
        self.prepareGeometryChange()
        pts = [self.src_node.out_port()] + self.waypoints + [self.dst_node.in_port()]
        self.path = build_smooth_orthogonal_path(pts, corner_radius=12.0)

    def show_handles(self):
        self.hide_handles()
        scene = self.scene()
        if not scene or getattr(scene, "read_only", False):
            return
        for idx, pt in enumerate(self.waypoints):
            h = PipeVertexHandle(self, idx, pt)
            scene.addItem(h)
            self.handles.append(h)

    def hide_handles(self):
        scene = self.scene()
        for h in self.handles:
            if scene and h.scene() == scene:
                scene.removeItem(h)
        self.handles.clear()

    def remove_waypoint(self, index: int):
        if 0 <= index < len(self.waypoints):
            self.waypoints.pop(index)
            self.rebuild_path()
            self.show_handles()

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemSelectedHasChanged:
            if value:
                self.show_handles()
            else:
                self.hide_handles()
        return super().itemChange(change, value)

    def mouseDoubleClickEvent(self, event):
        scene = self.scene()
        if scene and not getattr(scene, "read_only", False):
            new_pt = snap_to_grid(event.scenePos())
            all_pts = [self.src_node.out_port()] + self.waypoints + [self.dst_node.in_port()]
            best_idx = len(self.waypoints)
            best_dist = float("inf")
            for i in range(len(all_pts) - 1):
                mid = (all_pts[i] + all_pts[i + 1]) / 2.0
                d = (mid - new_pt).manhattanLength()
                if d < best_dist:
                    best_dist = d
                    best_idx = i
            self.waypoints.insert(best_idx, new_pt)
            self.rebuild_path()
            self.setSelected(True)
            self.show_handles()
        super().mouseDoubleClickEvent(event)

    def boundingRect(self):
        return self.path.boundingRect().adjusted(-25, -25, 25, 25)

    def advance_flow(self, dt_sec, speed_factor=1.0):
        if self.current_flow > 0.01 and speed_factor > 0.0:
            speed = min(4.5, max(0.35, (self.current_flow / 18.0) * speed_factor))
            self.dash_offset -= speed
            if self.dash_offset < -1000:
                self.dash_offset = 0.0
        self.update()

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)

        outer_w = 7 if self.diameter_mm <= 50 else (9 if self.diameter_mm <= 110 else 12)
        inner_w = outer_w - 3

        wall_color = QColor("#38bdf8") if self.isSelected() else QColor("#334155")
        painter.setPen(QPen(wall_color, outer_w, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        painter.drawPath(self.path)

        painter.setPen(QPen(QColor("#0f172a"), inner_w, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        painter.drawPath(self.path)

        is_flowing = self.current_flow > 0.01
        c = QColor(self.flow_color)
        c.setAlpha(255 if is_flowing else 55)
        flow_pen = QPen(c, inner_w - 1, Qt.CustomDashLine, Qt.FlatCap, Qt.RoundJoin)
        flow_pen.setDashPattern([4.0, 3.0])
        flow_pen.setDashOffset(self.dash_offset)
        painter.setPen(flow_pen)
        painter.drawPath(self.path)

        mid = self.path.pointAtPercent(0.5)
        painter.setPen(QColor("#cbd5e1"))
        painter.setFont(QFont("Consolas", 8))
        lbl = f"Ø{self.diameter_mm}mm"
        if is_flowing:
            lbl += f" [{self.current_flow:.1f} m³/h]"
        painter.drawText(mid + QPointF(6, -7), lbl)


# ==============================================================================
# PLUMBING & CUSTOM SYMBOL NODE ITEM
# ==============================================================================

class PlumbingNodeItem(QGraphicsItem):
    DIMENSIONS = {
        "source":      (100, 50),
        "tank":        (100, 110),
        "motor":       (84, 60),
        "valve":       (60, 54),
        "check_valve": (60, 50),
        "meter":       (66, 60),
        "header":      (160, 64),
        "demand":      (136, 54),
    }

    def __init__(self, node_id, node_type, x, y, label="", capacity=40.0, volume=20.0,
                 rated_flow=20.0, active=True, custom_spec=None):
        super().__init__()
        self.node_id = node_id
        self.node_type = node_type
        self.custom_spec = custom_spec

        if self.custom_spec:
            self.w, self.h = (72, 72)
        else:
            self.w, self.h = self.DIMENSIONS[node_type]

        self.label = label or (custom_spec["name"] if custom_spec else node_type.replace("_", " ").title())
        self.capacity = capacity
        self.volume = volume
        self.rated_flow = rated_flow
        self.active = active
        self.current_flow = 0.0
        self.totalizer_m3 = 0.0
        self.alarm = False

        self.rotor_angle = 0.0
        self.drag_start_pos = None
        self.connected_pipes = []
        self.hovered_port = None

        self.custom_pixmap = None
        self.custom_svg_renderer = None
        if self.custom_spec:
            raw = base64.b64decode(self.custom_spec["b64_data"])
            if self.custom_spec["ext"] == ".svg":
                self.custom_svg_renderer = QSvgRenderer(QByteArray(raw))
            else:
                img = QImage.fromData(raw)
                self.custom_pixmap = QPixmap.fromImage(img)

        self.setPos(snap_to_grid(QPointF(x, y)))
        self.setFlags(
            QGraphicsItem.ItemIsMovable |
            QGraphicsItem.ItemIsSelectable |
            QGraphicsItem.ItemSendsGeometryChanges
        )
        self.setCursor(Qt.OpenHandCursor)

    def in_port(self) -> QPointF:
        return self.pos() + QPointF(0, self.h / 2)

    def out_port(self) -> QPointF:
        return self.pos() + QPointF(self.w, self.h / 2)

    def boundingRect(self):
        return QRectF(-26, -24, self.w + 52, self.h + 48)

    def advance_animation(self, is_running: bool):
        if not is_running:
            return
        if self.node_type == "motor" and self.active and self.current_flow > 0.1:
            self.rotor_angle = (self.rotor_angle + 22.0) % 360.0
        elif self.node_type == "meter" and self.current_flow > 0.1:
            self.rotor_angle = (self.rotor_angle + self.current_flow * 0.8) % 360.0

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemPositionChange and self.scene():
            return snap_to_grid(value)
        elif change == QGraphicsItem.ItemPositionHasChanged:
            for p in self.connected_pipes:
                p.rebuild_path()
        return super().itemChange(change, value)

    def mousePressEvent(self, event):
        scene = self.scene()
        if scene and getattr(scene, "tool_mode", "select") == "pipe":
            scene.handle_pipe_node_click(self)
            event.accept()
            return

        if event.button() == Qt.LeftButton:
            self.drag_start_pos = QPointF(self.pos())
            can_operate = not getattr(scene, "viewer_only", False)
            if can_operate and self.node_type in ("motor", "valve"):
                self.active = not self.active
                self.update()
        super().mousePressEvent(event)

    def mouseReleaseEvent(self, event):
        super().mouseReleaseEvent(event)
        if self.drag_start_pos is not None and self.pos() != self.drag_start_pos:
            scene = self.scene()
            if scene and hasattr(scene, "undo_stack") and not getattr(scene, "read_only", False):
                scene.undo_stack.push(MoveNodeCommand(self, self.drag_start_pos, self.pos()))
        self.drag_start_pos = None

    def mouseDoubleClickEvent(self, event):
        scene = self.scene()
        if scene and getattr(scene, "read_only", False):
            return
        dlg = PropertyDialog(self)
        if dlg.exec() == QDialog.Accepted:
            dlg.apply_changes()
            scene.undo_stack.setClean() if False else None
            if hasattr(scene, "mark_dirty_callback") and scene.mark_dirty_callback:
                scene.mark_dirty_callback()
        super().mouseDoubleClickEvent(event)

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)

        if self.isSelected():
            painter.setPen(QPen(QColor("#38bdf8"), 1.5, Qt.DashLine))
            painter.setBrush(Qt.NoBrush)
            painter.drawRoundedRect(QRectF(-5, -5, self.w + 10, self.h + 10), 4, 4)

        if self.custom_spec:
            self._paint_custom_symbol(painter)
        elif self.node_type == "tank":
            self._paint_realistic_tank(painter)
        elif self.node_type == "motor":
            self._paint_realistic_motor_pump(painter)
        elif self.node_type == "valve":
            self._paint_realistic_valve(painter)
        elif self.node_type == "check_valve":
            self._paint_realistic_check_valve(painter)
        elif self.node_type == "meter":
            self._paint_realistic_meter(painter)
        elif self.node_type == "source":
            self._paint_realistic_source(painter)
        elif self.node_type == "header":
            self._paint_realistic_header(painter)
        elif self.node_type == "demand":
            self._paint_realistic_demand(painter)

        scene = self.scene()
        pipe_mode = (scene is not None and getattr(scene, "tool_mode", "select") == "pipe")
        pipe_started = (pipe_mode and getattr(scene, "pipe_start_node", None) is not None)

        if self.node_type != "source":
            in_pt = QPointF(0, self.h / 2)
            if pipe_mode and pipe_started:
                is_hov = (self.hovered_port == "in")
                painter.setBrush(QBrush(QColor("#22c55e" if is_hov else "#0284c7")))
                painter.setPen(QPen(QColor("#ffffff"), 2))
                painter.drawEllipse(in_pt, 8 if is_hov else 6.5, 8 if is_hov else 6.5)
                painter.setPen(QColor("#38bdf8"))
                painter.setFont(QFont("Consolas", 7, QFont.Bold))
                painter.drawText(QRectF(-24, self.h / 2 - 18, 24, 12), Qt.AlignCenter, "IN")
            else:
                painter.setBrush(QBrush(QColor("#cbd5e1")))
                painter.setPen(QPen(QColor("#0f172a"), 1))
                painter.drawEllipse(in_pt, 3.5, 3.5)

        if self.node_type != "demand":
            out_pt = QPointF(self.w, self.h / 2)
            if pipe_mode and not pipe_started:
                is_hov = (self.hovered_port == "out")
                painter.setBrush(QBrush(QColor("#22c55e" if is_hov else "#f59e0b")))
                painter.setPen(QPen(QColor("#ffffff"), 2))
                painter.drawEllipse(out_pt, 8 if is_hov else 6.5, 8 if is_hov else 6.5)
                painter.setPen(QColor("#fbbf24"))
                painter.setFont(QFont("Consolas", 7, QFont.Bold))
                painter.drawText(QRectF(self.w, self.h / 2 - 18, 26, 12), Qt.AlignCenter, "OUT")
            else:
                painter.setBrush(QBrush(QColor("#cbd5e1")))
                painter.setPen(QPen(QColor("#0f172a"), 1))
                painter.drawEllipse(out_pt, 3.5, 3.5)

    def _paint_custom_symbol(self, painter):
        border = QColor("#22c55e") if self.active else QColor("#ef4444")
        painter.setBrush(QBrush(QColor("#182030")))
        painter.setPen(QPen(border, 1.8))
        painter.drawRoundedRect(QRectF(2, 2, self.w - 4, self.h - 4), 6, 6)

        target = QRectF(8, 8, self.w - 16, self.h - 16)
        if self.custom_svg_renderer:
            self.custom_svg_renderer.render(painter, target)
        elif self.custom_pixmap:
            painter.drawPixmap(target.toRect(), self.custom_pixmap)

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(-20, -18, self.w + 40, 14), Qt.AlignCenter, self.label)

        sub = f"{self.volume:.1f}/{self.capacity:.0f}m³" if self.node_type == "tank" else (
            "ON" if self.active else "OFF"
        )
        painter.setPen(QColor("#94a3b8"))
        painter.setFont(QFont("Consolas", 7))
        painter.drawText(QRectF(-20, self.h + 2, self.w + 40, 14), Qt.AlignCenter, sub)

    def _paint_realistic_tank(self, painter):
        painter.setPen(QPen(QColor("#475569"), 4))
        painter.drawLine(14, self.h - 6, 14, self.h + 4)
        painter.drawLine(self.w - 14, self.h - 6, self.w - 14, self.h + 4)

        body_rect = QRectF(4, 10, self.w - 8, self.h - 16)
        grad = QLinearGradient(body_rect.left(), 0, body_rect.right(), 0)
        grad.setColorAt(0.0, QColor("#1e293b"))
        grad.setColorAt(0.35, QColor("#334155"))
        grad.setColorAt(1.0, QColor("#0f172a"))

        border = QColor("#ef4444") if self.alarm else QColor("#64748b")
        painter.setBrush(QBrush(grad))
        painter.setPen(QPen(border, 2))
        painter.drawRoundedRect(body_rect, 8, 8)

        painter.setBrush(QBrush(QColor("#475569")))
        painter.drawRect(QRectF(self.w / 2 - 12, 4, 24, 6))

        pct = max(0.0, min(1.0, self.volume / max(0.1, self.capacity)))
        inner_h = body_rect.height() - 4
        bar_h = max(2.0, pct * inner_h)
        water_rect = QRectF(body_rect.left() + 2, body_rect.bottom() - 2 - bar_h, body_rect.width() - 4, bar_h)

        w_grad = QLinearGradient(water_rect.left(), 0, water_rect.right(), 0)
        if self.alarm:
            w_grad.setColorAt(0.0, QColor(220, 38, 38, 180))
            w_grad.setColorAt(1.0, QColor(185, 28, 28, 180))
        else:
            w_grad.setColorAt(0.0, QColor(2, 132, 199, 180))
            w_grad.setColorAt(0.5, QColor(56, 189, 248, 210))
            w_grad.setColorAt(1.0, QColor(3, 105, 161, 180))

        painter.setBrush(QBrush(w_grad))
        painter.setPen(Qt.NoPen)
        painter.drawRoundedRect(water_rect, 5, 5)

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(4, 22, self.w - 8, 18), Qt.AlignCenter, self.label)
        painter.setPen(QColor("#e2e8f0"))
        painter.setFont(QFont("Consolas", 8))
        painter.drawText(QRectF(4, 40, self.w - 8, 16), Qt.AlignCenter, f"{self.capacity:.0f} m³")
        painter.drawText(QRectF(-15, self.h + 5, self.w + 30, 16), Qt.AlignCenter,
                         f"{self.volume:.1f} m³ ({int(pct * 100)}%)")

    def _paint_realistic_motor_pump(self, painter):
        cy = self.h / 2
        motor_grad = QLinearGradient(0, cy - 16, 0, cy + 16)
        if self.active:
            motor_grad.setColorAt(0.0, QColor("#15803d"))
            motor_grad.setColorAt(0.4, QColor("#22c55e"))
            motor_grad.setColorAt(1.0, QColor("#14532d"))
        else:
            motor_grad.setColorAt(0.0, QColor("#334155"))
            motor_grad.setColorAt(0.4, QColor("#64748b"))
            motor_grad.setColorAt(1.0, QColor("#1e293b"))

        painter.setBrush(QBrush(motor_grad))
        painter.setPen(QPen(QColor("#0f172a"), 1.5))
        painter.drawRoundedRect(QRectF(6, cy - 15, 36, 30), 4, 4)

        painter.setPen(QPen(QColor("#0f172a"), 1))
        for fy in (-9, -3, 3, 9):
            painter.drawLine(10, int(cy + fy), 38, int(cy + fy))

        painter.setBrush(QBrush(QColor("#475569")))
        painter.drawRect(QRectF(18, cy - 21, 12, 6))
        painter.setBrush(QBrush(QColor("#94a3b8")))
        painter.drawRect(QRectF(42, cy - 4, 8, 8))

        volute_cx = 62
        painter.setBrush(QBrush(QColor("#0284c7" if self.active else "#475569")))
        painter.setPen(QPen(QColor("#e2e8f0"), 1.2))
        painter.drawRect(QRectF(volute_cx, cy - 6, self.w - volute_cx, 12))

        vol_grad = QRadialGradient(volute_cx - 3, cy - 3, 20)
        if self.active:
            vol_grad.setColorAt(0.0, QColor("#38bdf8"))
            vol_grad.setColorAt(1.0, QColor("#0369a1"))
        else:
            vol_grad.setColorAt(0.0, QColor("#64748b"))
            vol_grad.setColorAt(1.0, QColor("#334155"))

        painter.setBrush(QBrush(vol_grad))
        painter.setPen(QPen(QColor("#f8fafc"), 1.5))
        painter.drawEllipse(QPointF(volute_cx, cy), 17, 17)

        painter.save()
        painter.translate(volute_cx, cy)
        painter.rotate(self.rotor_angle)
        painter.setPen(QPen(QColor("#0f172a"), 2))
        for deg in (0, 60, 120):
            rad = math.radians(deg)
            dx, dy = math.cos(rad) * 11, math.sin(rad) * 11
            painter.drawLine(QPointF(-dx, -dy), QPointF(dx, dy))
        painter.setBrush(QBrush(QColor("#f8fafc")))
        painter.drawEllipse(QPointF(0, 0), 3, 3)
        painter.restore()

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(-15, -20, self.w + 30, 15), Qt.AlignCenter, self.label)
        status = f"RUN {self.current_flow:.0f}m³/h" if self.active else "STOPPED"
        painter.setPen(QColor("#4ade80" if self.active else "#f87171"))
        painter.setFont(QFont("Consolas", 7, QFont.Bold))
        painter.drawText(QRectF(-15, self.h + 2, self.w + 30, 14), Qt.AlignCenter, status)

    def _paint_realistic_valve(self, painter):
        cx, cy = self.w / 2, self.h / 2
        painter.setBrush(QBrush(QColor("#475569")))
        painter.setPen(QPen(QColor("#0f172a"), 1.2))
        painter.drawRect(QRectF(4, cy - 11, 5, 22))
        painter.drawRect(QRectF(self.w - 9, cy - 11, 5, 22))

        body_col = QColor("#16a34a") if self.active else QColor("#dc2626")
        painter.setBrush(QBrush(body_col))
        painter.setPen(QPen(QColor("#f8fafc"), 1.4))
        painter.drawEllipse(QPointF(cx, cy), 12, 12)

        painter.setPen(QPen(QColor("#cbd5e1"), 2.5))
        painter.drawLine(int(cx), int(cy - 12), int(cx), int(cy - 21))
        if self.active:
            painter.setPen(QPen(QColor("#4ade80"), 3.5))
            painter.drawLine(int(cx - 12), int(cy - 21), int(cx + 12), int(cy - 21))
        else:
            painter.setPen(QPen(QColor("#ef4444"), 3.5))
            painter.drawLine(int(cx - 4), int(cy - 24), int(cx + 4), int(cy - 18))

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(-20, self.h + 2, self.w + 40, 14), Qt.AlignCenter,
                         f"{self.label} ({'OPEN' if self.active else 'SHUT'})")

    def _paint_realistic_check_valve(self, painter):
        cx, cy = self.w / 2, self.h / 2
        painter.setBrush(QBrush(QColor("#334155")))
        painter.setPen(QPen(QColor("#94a3b8"), 1.5))
        painter.drawRect(QRectF(6, cy - 11, 5, 22))
        painter.drawRect(QRectF(self.w - 11, cy - 11, 5, 22))
        painter.drawRoundedRect(QRectF(11, cy - 13, self.w - 22, 26), 4, 4)

        hinge = QPointF(cx - 7, cy - 8)
        angle = -55 if self.current_flow > 0.1 else -10
        rad = math.radians(angle)
        tip = QPointF(hinge.x() + math.cos(rad) * 16, hinge.y() - math.sin(rad) * 16)

        painter.setPen(QPen(QColor("#38bdf8"), 2.5))
        painter.drawLine(hinge, tip)
        painter.setBrush(QBrush(QColor("#f8fafc")))
        painter.drawEllipse(hinge, 2.5, 2.5)

        painter.setPen(QColor("#e2e8f0"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(-20, -18, self.w + 40, 14), Qt.AlignCenter, self.label)
        painter.setPen(QColor("#38bdf8"))
        painter.setFont(QFont("Consolas", 7))
        painter.drawText(QRectF(-20, self.h + 2, self.w + 40, 14), Qt.AlignCenter, "NRV →")

    def _paint_realistic_meter(self, painter):
        cx, cy = self.w / 2, self.h / 2
        painter.setBrush(QBrush(QColor("#b45309")))
        painter.setPen(QPen(QColor("#f59e0b"), 1.3))
        painter.drawRect(QRectF(5, cy - 11, 5, 22))
        painter.drawRect(QRectF(self.w - 10, cy - 11, 5, 22))
        painter.drawRect(QRectF(10, cy - 7, self.w - 20, 14))

        painter.setBrush(QBrush(QColor("#0f172a")))
        painter.setPen(QPen(QColor("#f59e0b"), 2))
        painter.drawEllipse(QPointF(cx, cy), 19, 19)

        rad = math.radians(self.rotor_angle)
        painter.setBrush(QBrush(QColor("#22c55e")))
        painter.setPen(Qt.NoPen)
        painter.drawEllipse(QPointF(cx + math.cos(rad) * 13, cy + math.sin(rad) * 13), 2.2, 2.2)

        painter.setPen(QColor("#fbbf24"))
        painter.setFont(QFont("Consolas", 7, QFont.Bold))
        painter.drawText(QRectF(0, cy - 11, self.w, 12), Qt.AlignCenter, f"{self.current_flow:.1f}")
        painter.setPen(QColor("#94a3b8"))
        painter.setFont(QFont("Consolas", 6))
        painter.drawText(QRectF(0, cy + 1, self.w, 11), Qt.AlignCenter, "m³/h")

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(-25, -18, self.w + 50, 14), Qt.AlignCenter, self.label)
        painter.setPen(QColor("#f59e0b"))
        painter.setFont(QFont("Consolas", 7))
        painter.drawText(QRectF(-25, self.h + 2, self.w + 50, 14), Qt.AlignCenter,
                         f"Σ {self.totalizer_m3:.2f} m³")

    def _paint_realistic_source(self, painter):
        grad = QLinearGradient(0, 0, 0, self.h)
        grad.setColorAt(0.0, QColor("#0e7490"))
        grad.setColorAt(1.0, QColor("#164e63"))
        painter.setBrush(QBrush(grad))
        painter.setPen(QPen(QColor("#22d3ee"), 2))
        painter.drawRoundedRect(QRectF(4, 4, self.w - 8, self.h - 8), 6, 6)

        painter.setPen(QColor("#ffffff"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(6, 7, self.w - 12, 18), Qt.AlignCenter, self.label)
        painter.setPen(QColor("#cffafe"))
        painter.setFont(QFont("Consolas", 8))
        painter.drawText(QRectF(6, 25, self.w - 12, 16), Qt.AlignCenter, f"{self.rated_flow:.1f} m³/h")

    def _paint_realistic_header(self, painter):
        body = QRectF(8, 16, self.w - 16, self.h - 24)
        grad = QLinearGradient(0, body.top(), 0, body.bottom())
        grad.setColorAt(0.0, QColor("#1e293b"))
        grad.setColorAt(0.45, QColor("#475569"))
        grad.setColorAt(1.0, QColor("#0f172a"))

        painter.setBrush(QBrush(grad))
        painter.setPen(QPen(QColor("#22c55e"), 1.8))
        painter.drawRoundedRect(body, 6, 6)

        gx = self.w / 2
        painter.setPen(QPen(QColor("#94a3b8"), 2))
        painter.drawLine(int(gx), 10, int(gx), 16)
        painter.setBrush(QBrush(QColor("#f8fafc")))
        painter.setPen(QPen(QColor("#0f172a"), 1.5))
        painter.drawEllipse(QPointF(gx, 6), 7, 7)
        painter.setPen(QPen(QColor("#ef4444"), 1.5))
        painter.drawLine(QPointF(gx, 6), QPointF(gx + 3, 3))

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(body, Qt.AlignCenter, f"{self.label}\n({self.current_flow:.1f} m³/h)")

    def _paint_realistic_demand(self, painter):
        grad = QLinearGradient(0, 0, 0, self.h)
        grad.setColorAt(0.0, QColor("#31102f"))
        grad.setColorAt(1.0, QColor("#1e1b4b"))
        painter.setBrush(QBrush(grad))
        painter.setPen(QPen(QColor("#ec4899"), 1.8))
        painter.drawRoundedRect(QRectF(4, 4, self.w - 8, self.h - 8), 6, 6)

        painter.setPen(QColor("#f8fafc"))
        painter.setFont(QFont("Segoe UI", 8, QFont.Bold))
        painter.drawText(QRectF(6, 8, self.w - 12, 18), Qt.AlignCenter, self.label)
        painter.setPen(QColor("#f9a8d4"))
        painter.setFont(QFont("Consolas", 8))
        painter.drawText(QRectF(6, 26, self.w - 12, 16), Qt.AlignCenter,
                         f"{self.current_flow:.1f} / {self.rated_flow:.1f} m³/h")


# ==============================================================================
# DRAG-AND-DROP COMPONENT PALETTE
# ==============================================================================

class ComponentPaletteList(QListWidget):
    BUILTINS = [
        ("source",      "Water Source",  "#06b6d4"),
        ("tank",        "Water Tank / Sump",        "#0284c7"),
        ("motor",       "Centrifugal Motor Pump",   "#22c55e"),
        ("valve",       "Isolation Gate Valve",     "#16a34a"),
        ("check_valve", "Non-Return Valve (NRV)",   "#38bdf8"),
        ("meter",       "Digital Water Meter",      "#f59e0b"),
        ("header",      "Distribution Header",      "#4ade80"),
        ("demand",      "Process / Demand Load",    "#ec4899"),
    ]

    def __init__(self, parent=None):
        super().__init__(parent)
        self.custom_symbols = {}
        self.setDragEnabled(True)
        self.setSelectionMode(QAbstractItemView.SingleSelection)
        self.setStyleSheet("""
            QListWidget {
                background-color: #121722; border: none; padding: 6px; outline: none;
            }
            QListWidget::item {
                background-color: #182030; border: 1px solid #2d3a52;
                border-radius: 6px; padding: 9px 8px; margin-bottom: 5px;
                color: #f1f5f9; font-weight: 600; font-size: 12px;
            }
            QListWidget::item:hover {
                background-color: #243047; border-color: #38bdf8;
            }
        """)

        for comp_type, title, color_hex in self.BUILTINS:
            self._add_palette_entry(comp_type, title, color_hex)

    def _add_palette_entry(self, payload_key, title, color_hex, icon_pix=None):
        item = QListWidgetItem(title)
        item.setData(Qt.UserRole, payload_key)
        if icon_pix:
            item.setIcon(icon_pix)
        else:
            pix = QPixmap(16, 16)
            pix.fill(Qt.transparent)
            p = QPainter(pix)
            p.setRenderHint(QPainter.Antialiasing)
            p.setBrush(QBrush(QColor(color_hex)))
            p.setPen(Qt.NoPen)
            p.drawRoundedRect(1, 1, 14, 14, 4, 4)
            p.end()
            item.setIcon(pix)
        self.addItem(item)

    def register_custom_symbol(self, spec: dict):
        sid = spec["symbol_id"]
        self.custom_symbols[sid] = spec
        self._add_palette_entry(sid, f"★ {spec['name']}", "#a855f7")

    def startDrag(self, supportedActions):
        item = self.currentItem()
        if not item:
            return
        key = item.data(Qt.UserRole)
        payload = {"key": key}
        if key in self.custom_symbols:
            payload["custom_spec"] = self.custom_symbols[key]

        mime = QMimeData()
        mime.setData(MIME_TYPE, json.dumps(payload).encode("utf-8"))

        drag = QDrag(self)
        drag.setMimeData(mime)

        if "custom_spec" in payload:
            preview_node = PlumbingNodeItem("prev", payload["custom_spec"]["behavior"], 0, 0, custom_spec=payload["custom_spec"])
        else:
            preview_node = PlumbingNodeItem("prev", key, 0, 0)

        pix = QPixmap(preview_node.w + 20, preview_node.h + 24)
        pix.fill(Qt.transparent)
        painter = QPainter(pix)
        painter.translate(10, 12)
        preview_node.paint(painter, None)
        painter.end()

        drag.setPixmap(pix)
        drag.setHotSpot(QPointF(pix.width() / 2, pix.height() / 2).toPoint())
        drag.exec(Qt.CopyAction)


# ==============================================================================
# ZOOMABLE & PANNABLE GRAPHICS VIEW
# ==============================================================================

class ScadaGraphicsView(QGraphicsView):
    def __init__(self, scene, zoom_callback=None):
        super().__init__(scene)
        self.zoom_callback = zoom_callback
        self.zoom_level = 1.0
        self.min_zoom = 0.30
        self.max_zoom = 3.00
        self._panning = False
        self._pan_start = QPointF()

        self.setRenderHint(QPainter.Antialiasing)
        self.setAcceptDrops(True)
        self.setMouseTracking(True)
        self.setFrameShape(QFrame.NoFrame)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorUnderMouse)

    def apply_zoom_factor(self, factor: float):
        new_zoom = self.zoom_level * factor
        if new_zoom < self.min_zoom:
            factor = self.min_zoom / self.zoom_level
            self.zoom_level = self.min_zoom
        elif new_zoom > self.max_zoom:
            factor = self.max_zoom / self.zoom_level
            self.zoom_level = self.max_zoom
        else:
            self.zoom_level = new_zoom

        self.scale(factor, factor)
        if self.zoom_callback:
            self.zoom_callback(self.zoom_level)

    def reset_zoom(self):
        self.resetTransform()
        self.zoom_level = 1.0
        if self.zoom_callback:
            self.zoom_callback(self.zoom_level)

    def fit_diagram(self):
        items_rect = self.scene().itemsBoundingRect()
        if items_rect.isEmpty():
            self.reset_zoom()
            return
        self.fitInView(items_rect.adjusted(-40, -40, 40, 40), Qt.KeepAspectRatio)
        self.zoom_level = self.transform().m11()
        if self.zoom_callback:
            self.zoom_callback(self.zoom_level)

    def wheelEvent(self, event):
        if event.angleDelta().y() > 0:
            self.apply_zoom_factor(1.15)
        else:
            self.apply_zoom_factor(1.0 / 1.15)
        event.accept()

    def mousePressEvent(self, event):
        if event.button() == Qt.MiddleButton:
            self._panning = True
            self._pan_start = event.position()
            self.setCursor(Qt.ClosedHandCursor)
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._panning:
            delta = event.position() - self._pan_start
            self._pan_start = event.position()
            self.horizontalScrollBar().setValue(int(self.horizontalScrollBar().value() - delta.x()))
            self.verticalScrollBar().setValue(int(self.verticalScrollBar().value() - delta.y()))
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.MiddleButton and self._panning:
            self._panning = False
            self.setCursor(Qt.ArrowCursor)
            event.accept()
            return
        super().mouseReleaseEvent(event)


# ==============================================================================
# INTERACTIVE CAD SCENE
# ==============================================================================

class InteractiveScadaScene(QGraphicsScene):
    def __init__(self, width, height, undo_stack: QUndoStack, status_callback):
        super().__init__(0, 0, width, height)
        self.undo_stack = undo_stack
        self.status_callback = status_callback
        self.tool_mode = "select"
        self.read_only = False
        self.viewer_only = False
        self.mark_dirty_callback = None

        self.pipe_start_node = None
        self.pipe_waypoints = []
        self.temp_line_path = None
        self.snap_target_node = None

    def set_tool(self, mode):
        if self.read_only and mode != "select":
            self.status_callback("Read-Only Mode: Switch to Admin role to edit piping or components.")
            return
        self.tool_mode = mode
        self._cancel_pipe_drawing()
        self._clear_port_highlights()

        for item in self.items():
            if isinstance(item, PlumbingNodeItem):
                item.update()

        if mode == "select":
            self.status_callback("Select Mode: Drag equipment | Click Pipe to edit bends | Press ESC to clear selection")
        elif mode == "pipe":
            self.status_callback("Pipe Router: Click an orange OUT port to start, click grid for bends, click blue IN port (ESC to exit)")

    def _clear_port_highlights(self):
        self.snap_target_node = None
        for item in self.items():
            if isinstance(item, PlumbingNodeItem) and item.hovered_port is not None:
                item.hovered_port = None
                item.update()

    def _cancel_pipe_drawing(self):
        self.pipe_start_node = None
        self.pipe_waypoints = []
        self._clear_port_highlights()
        if self.temp_line_path is not None:
            if self.temp_line_path.scene() == self:
                self.removeItem(self.temp_line_path)
            self.temp_line_path = None

    def abort_current_action(self):
        was_routing = (self.tool_mode == "pipe" or self.pipe_start_node is not None)
        self._cancel_pipe_drawing()
        self.clearSelection()
        if was_routing:
            self.set_tool("select")
        self.status_callback("Cleared selection & exited pipe routing (ESC).")

    def dragEnterEvent(self, event):
        if not self.read_only and event.mimeData().hasFormat(MIME_TYPE):
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)

    def dragMoveEvent(self, event):
        if not self.read_only and event.mimeData().hasFormat(MIME_TYPE):
            event.acceptProposedAction()
        else:
            super().dragMoveEvent(event)

    def dropEvent(self, event):
        if not self.read_only and event.mimeData().hasFormat(MIME_TYPE):
            payload = json.loads(bytes(event.mimeData().data(MIME_TYPE)).decode("utf-8"))
            pos = snap_to_grid(event.scenePos())
            if "custom_spec" in payload:
                spec = payload["custom_spec"]
                node = PlumbingNodeItem(
                    str(uuid.uuid4())[:8], spec["behavior"], pos.x(), pos.y(),
                    label=spec["name"], custom_spec=spec
                )
            else:
                node = PlumbingNodeItem(str(uuid.uuid4())[:8], payload["key"], pos.x(), pos.y())

            self.undo_stack.push(AddNodeCommand(self, node))
            self.status_callback(f"Placed {node.label} at ({int(pos.x())}, {int(pos.y())})")
            event.acceptProposedAction()
        else:
            super().dropEvent(event)

    def _find_nearest_port(self, scene_pos: QPointF, want_in_port: bool, radius: float = 26.0):
        best_node = None
        best_dist = radius
        for item in self.items():
            if not isinstance(item, PlumbingNodeItem):
                continue
            if want_in_port:
                if item.node_type == "source" or item == self.pipe_start_node:
                    continue
                port_pt = item.in_port()
            else:
                if item.node_type == "demand":
                    continue
                port_pt = item.out_port()

            dist = math.hypot(scene_pos.x() - port_pt.x(), scene_pos.y() - port_pt.y())
            if dist <= best_dist:
                best_dist = dist
                best_node = item
        return best_node

    def handle_pipe_node_click(self, node: PlumbingNodeItem):
        if self.read_only:
            return
        if self.pipe_start_node is None:
            if node.node_type == "demand":
                self.status_callback("Cannot start a pipe from a Demand Sink.")
                return
            self.pipe_start_node = node
            self.pipe_waypoints = []
            self.temp_line_path = self.addPath(QPainterPath(), QPen(QColor("#38bdf8"), 3.0, Qt.DashLine))
            for item in self.items():
                if isinstance(item, PlumbingNodeItem):
                    item.hovered_port = None
                    item.update()
            self.status_callback(f"Routing from '{node.label}' OUT... Click grid for bends or click any blue IN port (ESC to cancel).")
        elif node != self.pipe_start_node:
            if node.node_type == "source":
                self.status_callback("Cannot connect a pipe INTO a Water Source.")
                return
            dias = ["32", "50", "63", "75", "110", "160", "225"]
            dia_str, ok = QInputDialog.getItem(
                None, "Pipe Specifications", "Select Nominal Diameter (mm):", dias, 3, False
            )
            if ok:
                color = "#06b6d4"
                if self.pipe_start_node.node_type in ("motor", "tank"):
                    color = "#eab308"
                elif self.pipe_start_node.node_type == "header":
                    color = "#ec4899"

                pipe = PipeEdgeItem(
                    str(uuid.uuid4())[:8],
                    self.pipe_start_node,
                    node,
                    [(p.x(), p.y()) for p in self.pipe_waypoints],
                    int(dia_str),
                    color
                )
                self.undo_stack.push(AddPipeCommand(self, pipe))
                self.status_callback(f"Connected {self.pipe_start_node.label} → {node.label} (Ø{dia_str}mm). Ready for next pipe or press ESC.")

            self._cancel_pipe_drawing()
            for item in self.items():
                if isinstance(item, PlumbingNodeItem):
                    item.update()

    def mousePressEvent(self, event):
        if event.button() == Qt.RightButton and self.tool_mode == "pipe":
            self.abort_current_action()
            return

        if self.tool_mode == "pipe" and event.button() == Qt.LeftButton:
            if self.pipe_start_node is None:
                near_out = self._find_nearest_port(event.scenePos(), want_in_port=False)
                if near_out:
                    self.handle_pipe_node_click(near_out)
                    return
            else:
                near_in = self._find_nearest_port(event.scenePos(), want_in_port=True)
                if near_in:
                    self.handle_pipe_node_click(near_in)
                    return

                item = self.itemAt(event.scenePos(), self.views()[0].transform())
                if not isinstance(item, PlumbingNodeItem):
                    pos = snap_to_grid(event.scenePos())
                    self.pipe_waypoints.append(pos)
                    self._update_temp_pipe(pos)
                    return

        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self.tool_mode == "pipe":
            self._clear_port_highlights()
            if self.pipe_start_node is None:
                near_out = self._find_nearest_port(event.scenePos(), want_in_port=False)
                if near_out:
                    near_out.hovered_port = "out"
                    near_out.update()
            else:
                near_in = self._find_nearest_port(event.scenePos(), want_in_port=True)
                if near_in:
                    near_in.hovered_port = "in"
                    near_in.update()
                    self._update_temp_pipe(near_in.in_port())
                else:
                    self._update_temp_pipe(snap_to_grid(event.scenePos()))
        super().mouseMoveEvent(event)

    def _update_temp_pipe(self, target_pt: QPointF):
        if not self.temp_line_path or not self.pipe_start_node:
            return
        pts = [self.pipe_start_node.out_port()] + self.pipe_waypoints + [target_pt]
        smooth_preview = build_smooth_orthogonal_path(pts, corner_radius=12.0)
        self.temp_line_path.setPath(smooth_preview)

    def drawBackground(self, painter, rect):
        painter.fillRect(rect, QColor("#0d111a"))
        painter.setPen(QPen(QColor("#171e2e"), 1))
        left = int(rect.left()) - (int(rect.left()) % GRID_SIZE)
        top = int(rect.top()) - (int(rect.top()) % GRID_SIZE)
        for x in range(left, int(rect.right()), GRID_SIZE):
            painter.drawLine(x, int(rect.top()), x, int(rect.bottom()))
        for y in range(top, int(rect.bottom()), GRID_SIZE):
            painter.drawLine(int(rect.left()), y, int(rect.right()), y)


# ==============================================================================
# MAIN WORKSTATION WINDOW WITH PROJECT OPEN / SAVE / EXPORT SUITE
# ==============================================================================

class WaterScadaStudio(QMainWindow):
    def __init__(self, username: str, role: str, auth_manager: AuthManager):
        super().__init__()
        self.username = username
        self.role = role
        self.auth_manager = auth_manager
        self.sim_speed = 15.0
        self.sim_paused = False
        self.undo_stack = QUndoStack(self)

        # Project state tracking
        self.current_project_path = None
        self.is_dirty = False

        self.resize(1480, 850)
        self.setStyleSheet("background-color: #0b0e14; color: #e2e8f0;")

        central = QWidget()
        self.setCentralWidget(central)
        root_layout = QVBoxLayout(central)
        root_layout.setContentsMargins(0, 0, 0, 0)
        root_layout.setSpacing(0)

        self._build_topbar(root_layout)
        self._build_secondary_toolbar(root_layout)

        body_layout = QHBoxLayout()
        body_layout.setSpacing(0)
        root_layout.addLayout(body_layout)

        self.status_bar_lbl = QLabel("Ready.")
        self.status_bar_lbl.setStyleSheet(
            "background: #121722; color: #94a3b8; padding: 6px 14px; border-top: 1px solid #263044;"
        )
        root_layout.addWidget(self.status_bar_lbl)

        self.scene = InteractiveScadaScene(1800, 1000, self.undo_stack, self._set_status)
        self.scene.mark_dirty_callback = self._mark_dirty
        self._build_left_sidebar(body_layout)

        self.view = ScadaGraphicsView(self.scene, self._on_zoom_changed)
        body_layout.addWidget(self.view)

        self.undo_stack.cleanChanged.connect(self._on_clean_changed)

        self._apply_role_permissions()
        self._setup_shortcuts()
        self._load_default_plant()
        self.undo_stack.setClean()
        self._set_dirty(False)

        self.timer = QTimer(self)
        self.timer.timeout.connect(self._step_simulation)
        self.timer.start(50)

    def _update_window_title(self):
        proj_name = os.path.basename(self.current_project_path) if self.current_project_path else "Untitled_Plant.scada"
        dirty_mark = "*" if self.is_dirty else ""
        self.setWindowTitle(
            f"2D Water SCADA & Plumbing CAD — [{proj_name}{dirty_mark}] — ({self.username} | {self.role})"
        )

    def _set_dirty(self, dirty: bool):
        self.is_dirty = dirty
        self._update_window_title()

    def _mark_dirty(self):
        self._set_dirty(True)

    def _on_clean_changed(self, clean: bool):
        if not clean:
            self._set_dirty(True)

    def _confirm_discard_unsaved(self) -> bool:
        """Prompts user to save changes before replacing or closing a modified project."""
        if not self.is_dirty:
            return True
        proj_name = os.path.basename(self.current_project_path) if self.current_project_path else "Untitled_Plant.scada"
        reply = QMessageBox.question(
            self,
            "Unsaved Project Changes",
            f"Save changes to '{proj_name}' before continuing?",
            QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel,
            QMessageBox.Save
        )
        if reply == QMessageBox.Save:
            return self._save_project()
        elif reply == QMessageBox.Discard:
            return True
        return False

    def closeEvent(self, event):
        if self._confirm_discard_unsaved():
            event.accept()
        else:
            event.ignore()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.scene.abort_current_action()
            event.accept()
            return
        super().keyPressEvent(event)

    def _set_status(self, text):
        self.status_bar_lbl.setText(text)

    def _on_zoom_changed(self, zoom_val: float):
        self.zoom_lbl.setText(f"{int(round(zoom_val * 100))}%")

    def _apply_role_permissions(self):
        is_admin = (self.role == "Admin")
        is_viewer = (self.role == "Viewer")

        self.scene.read_only = not is_admin
        self.scene.viewer_only = is_viewer
        self.sidebar_frame.setVisible(is_admin)
        self.btn_undo.setVisible(is_admin)
        self.btn_redo.setVisible(is_admin)

        for item in self.scene.items():
            if isinstance(item, PlumbingNodeItem):
                item.setFlag(QGraphicsItem.ItemIsMovable, is_admin)

        self._update_window_title()
        if is_admin:
            self._set_status(f"Logged in as {self.username} (Admin): Full CAD, Project Open/Save, Export & Plant Control enabled.")
        elif self.role == "Operator":
            self._set_status(f"Logged in as {self.username} (Operator): Live Pump/Valve Control & Export enabled.")
        else:
            self._set_status(f"Logged in as {self.username} (Viewer): Read-Only Telemetry Monitoring.")

    def _switch_user(self):
        dlg = LoginDialog(self.auth_manager, self)
        if dlg.exec() == QDialog.Accepted:
            self.username = dlg.authenticated_user
            self.role = dlg.authenticated_role
            self.user_badge.setText(f"👤 {self.username} ({self.role})")
            self._apply_role_permissions()

    def _setup_shortcuts(self):
        new_act = QAction("New Project", self)
        new_act.setShortcut(QKeySequence.New)
        new_act.triggered.connect(self._new_project)
        self.addAction(new_act)

        open_act = QAction("Open Project", self)
        open_act.setShortcut(QKeySequence.Open)
        open_act.triggered.connect(self._open_project)
        self.addAction(open_act)

        save_act = QAction("Save Project", self)
        save_act.setShortcut(QKeySequence.Save)
        save_act.triggered.connect(self._save_project)
        self.addAction(save_act)

        save_as_act = QAction("Save Project As", self)
        save_as_act.setShortcut(QKeySequence.SaveAs)
        save_as_act.triggered.connect(self._save_project_as)
        self.addAction(save_as_act)

        undo_act = self.undo_stack.createUndoAction(self, "Undo")
        undo_act.setShortcut(QKeySequence.Undo)
        self.addAction(undo_act)

        redo_act = self.undo_stack.createRedoAction(self, "Redo")
        redo_act.setShortcut(QKeySequence.Redo)
        self.addAction(redo_act)

        del_act = QAction("Delete", self)
        del_act.setShortcut(QKeySequence.Delete)
        del_act.triggered.connect(self._delete_selected)
        self.addAction(del_act)

        zoom_in_act = QAction("Zoom In", self)
        zoom_in_act.setShortcut(QKeySequence.ZoomIn)
        zoom_in_act.triggered.connect(lambda: self.view.apply_zoom_factor(1.2))
        self.addAction(zoom_in_act)

        zoom_out_act = QAction("Zoom Out", self)
        zoom_out_act.setShortcut(QKeySequence.ZoomOut)
        zoom_out_act.triggered.connect(lambda: self.view.apply_zoom_factor(1.0 / 1.2))
        self.addAction(zoom_out_act)

    # ==========================================================================
    # TOP KPI BAR & PROJECT / EXPORT TOOLBAR
    # ==========================================================================
    def _build_topbar(self, parent_layout):
        bar = QFrame()
        bar.setFixedHeight(70)
        bar.setStyleSheet("background-color: #121722; border-bottom: 1px solid #263044;")
        layout = QHBoxLayout(bar)
        layout.setContentsMargins(14, 8, 14, 8)
        layout.setSpacing(8)

        self.kpi_inflow = self._make_kpi(layout, "TOTAL INFLOW", "0.0 m³/h", "#22c55e")
        self.kpi_demand = self._make_kpi(layout, "TOTAL DEMAND", "0.0 m³/h", "#38bdf8")
        self.kpi_stored = self._make_kpi(layout, "STORED VOLUME", "0.0 / 0 m³", "#f59e0b")

        self.alarm_lbl = QLabel("● SYSTEM NORMAL")
        self.alarm_lbl.setStyleSheet(
            "background: #132a1c; border: 1px solid #22c55e; color: #4ade80;"
            "border-radius: 6px; padding: 8px 12px; font-weight: bold;"
        )
        layout.addWidget(self.alarm_lbl)
        layout.addStretch()

        btn_style = (
            "background: #1e293b; border: 1px solid #475569; padding: 6px 10px;"
            "border-radius: 5px; font-weight: bold; font-size: 12px;"
        )

        # --- PROJECT MENU & DIRECT OPEN / SAVE BUTTONS ---
        proj_menu_btn = QPushButton("📁 Project ▾")
        proj_menu_btn.setCursor(Qt.PointingHandCursor)
        proj_menu_btn.setStyleSheet(
            "background: #1e3a8a; border: 1px solid #3b82f6; color: #eff6ff;"
            "padding: 6px 12px; border-radius: 5px; font-weight: bold; font-size: 12px;"
        )
        proj_menu = QMenu(self)
        proj_menu.setStyleSheet("""
            QMenu { background-color: #1e293b; color: #f8fafc; border: 1px solid #475569; padding: 4px; }
            QMenu::item { padding: 7px 18px; font-size: 12px; }
            QMenu::item:selected { background-color: #0284c7; }
        """)
        proj_menu.addAction("📄 New Blank Project (Ctrl+N)", self._new_project)
        proj_menu.addAction("🏭 Load Sample Plant Template", self._reset_to_sample_plant)
        proj_menu.addSeparator()
        proj_menu.addAction("📂 Open Project... (Ctrl+O)", self._open_project)
        proj_menu.addAction("💾 Save Project (Ctrl+S)", self._save_project)
        proj_menu.addAction("💾 Save Project As... (Ctrl+Shift+S)", self._save_project_as)
        proj_menu_btn.setMenu(proj_menu)
        layout.addWidget(proj_menu_btn)

        btn_open = QPushButton("📂 Open")
        btn_open.setToolTip("Open Project (Ctrl+O)")
        btn_open.setCursor(Qt.PointingHandCursor)
        btn_open.setStyleSheet(btn_style)
        btn_open.clicked.connect(self._open_project)
        layout.addWidget(btn_open)

        btn_save = QPushButton("💾 Save")
        btn_save.setToolTip("Save Project (Ctrl+S)")
        btn_save.setCursor(Qt.PointingHandCursor)
        btn_save.setStyleSheet(btn_style)
        btn_save.clicked.connect(self._save_project)
        layout.addWidget(btn_save)

        # --- UNDO / REDO ---
        self.btn_undo = QPushButton("↶ Undo")
        self.btn_redo = QPushButton("↷ Redo")
        self.btn_undo.clicked.connect(self.undo_stack.undo)
        self.btn_redo.clicked.connect(self.undo_stack.redo)
        self.undo_stack.canUndoChanged.connect(self.btn_undo.setEnabled)
        self.undo_stack.canRedoChanged.connect(self.btn_redo.setEnabled)
        self.btn_undo.setEnabled(False)
        self.btn_redo.setEnabled(False)

        for b in (self.btn_undo, self.btn_redo):
            b.setStyleSheet(btn_style)
            b.setCursor(Qt.PointingHandCursor)
            layout.addWidget(b)

        # --- EXPORT PROJECT MENU ---
        export_btn = QPushButton("📤 Export Project ▾")
        export_btn.setCursor(Qt.PointingHandCursor)
        export_btn.setStyleSheet(
            "background: #065f46; border: 1px solid #10b981; color: #ecfdf5;"
            "padding: 6px 12px; border-radius: 5px; font-weight: bold; font-size: 12px;"
        )
        export_menu = QMenu(self)
        export_menu.setStyleSheet("""
            QMenu { background-color: #1e293b; color: #f8fafc; border: 1px solid #475569; padding: 4px; }
            QMenu::item { padding: 7px 18px; font-size: 12px; }
            QMenu::item:selected { background-color: #0284c7; }
        """)
        export_menu.addAction("🖼 Export Schematic Image (.PNG)", self._export_png)
        export_menu.addAction("📄 Export Engineering Sheet (.PDF)", self._export_pdf)
        export_menu.addAction("📊 Export Telemetry & Meter Log (.CSV)", self._export_csv)
        export_menu.addSeparator()
        export_menu.addAction("📦 Export Standalone Project Package (.JSON)", self._export_project_package)
        export_btn.setMenu(export_menu)
        layout.addWidget(export_btn)

        # --- USER BADGE ---
        self.user_badge = QPushButton(f"👤 {self.username} ({self.role})")
        self.user_badge.setCursor(Qt.PointingHandCursor)
        self.user_badge.setStyleSheet(
            "background: #0f172a; border: 1px solid #38bdf8; color: #38bdf8;"
            "padding: 6px 12px; border-radius: 5px; font-weight: bold; font-size: 12px;"
        )
        self.user_badge.clicked.connect(self._switch_user)
        layout.addWidget(self.user_badge)

        parent_layout.addWidget(bar)

    def _build_secondary_toolbar(self, parent_layout):
        sub = QFrame()
        sub.setFixedHeight(44)
        sub.setStyleSheet("background-color: #0f141e; border-bottom: 1px solid #263044;")
        layout = QHBoxLayout(sub)
        layout.setContentsMargins(14, 4, 14, 4)
        layout.setSpacing(8)

        mini_btn = (
            "background: #1e293b; border: 1px solid #334155; padding: 4px 10px;"
            "border-radius: 4px; font-weight: bold; font-size: 11px; color: #e2e8f0;"
        )

        z_title = QLabel("CANVAS ZOOM:")
        z_title.setStyleSheet("color: #94a3b8; font-size: 11px; font-weight: bold;")
        layout.addWidget(z_title)

        btn_z_out = QPushButton("－ Zoom Out")
        btn_z_in = QPushButton("＋ Zoom In")
        btn_z_100 = QPushButton("100%")
        btn_z_fit = QPushButton("⛶ Fit Screen")

        self.zoom_lbl = QLabel("100%")
        self.zoom_lbl.setMinimumWidth(46)
        self.zoom_lbl.setAlignment(Qt.AlignCenter)
        self.zoom_lbl.setStyleSheet(
            "background: #182030; border: 1px solid #2d3a52; border-radius: 4px;"
            "padding: 3px 6px; color: #38bdf8; font-weight: bold; font-size: 11px;"
        )

        btn_z_out.clicked.connect(lambda: self.view.apply_zoom_factor(1.0 / 1.2))
        btn_z_in.clicked.connect(lambda: self.view.apply_zoom_factor(1.2))
        btn_z_100.clicked.connect(lambda: self.view.reset_zoom())
        btn_z_fit.clicked.connect(lambda: self.view.fit_diagram())

        for b in (btn_z_out, btn_z_in, btn_z_100, btn_z_fit):
            b.setStyleSheet(mini_btn)
            b.setCursor(Qt.PointingHandCursor)

        layout.addWidget(btn_z_out)
        layout.addWidget(self.zoom_lbl)
        layout.addWidget(btn_z_in)
        layout.addWidget(btn_z_100)
        layout.addWidget(btn_z_fit)

        sep = QFrame()
        sep.setFrameShape(QFrame.VLine)
        sep.setStyleSheet("color: #334155;")
        layout.addWidget(sep)

        s_title = QLabel("SIMULATION SPEED:")
        s_title.setStyleSheet("color: #94a3b8; font-size: 11px; font-weight: bold;")
        layout.addWidget(s_title)

        self.btn_pause = QPushButton("⏸ Pause")
        self.btn_pause.setCursor(Qt.PointingHandCursor)
        self.btn_pause.setStyleSheet(
            "background: #1e293b; border: 1px solid #f59e0b; color: #fbbf24;"
            "padding: 4px 10px; border-radius: 4px; font-weight: bold; font-size: 11px;"
        )
        self.btn_pause.clicked.connect(self._toggle_pause)
        layout.addWidget(self.btn_pause)

        self.speed_slider = QSlider(Qt.Horizontal)
        self.speed_slider.setRange(1, 100)
        self.speed_slider.setValue(int(self.sim_speed))
        self.speed_slider.setFixedWidth(150)
        self.speed_slider.setCursor(Qt.PointingHandCursor)
        self.speed_slider.setStyleSheet("""
            QSlider::groove:horizontal { height: 6px; background: #1e293b; border-radius: 3px; }
            QSlider::handle:horizontal {
                background: #38bdf8; width: 14px; height: 14px; margin: -4px 0; border-radius: 7px;
            }
        """)
        self.speed_slider.valueChanged.connect(self._on_speed_slider_changed)
        layout.addWidget(self.speed_slider)

        self.speed_val_lbl = QLabel("15x")
        self.speed_val_lbl.setMinimumWidth(42)
        self.speed_val_lbl.setAlignment(Qt.AlignCenter)
        self.speed_val_lbl.setStyleSheet(
            "background: #182030; border: 1px solid #2d3a52; border-radius: 4px;"
            "padding: 3px 6px; color: #22c55e; font-weight: bold; font-size: 11px;"
        )
        layout.addWidget(self.speed_val_lbl)

        for preset in (1, 10, 30, 60, 100):
            pb = QPushButton(f"{preset}x")
            pb.setCursor(Qt.PointingHandCursor)
            pb.setStyleSheet(mini_btn)
            pb.clicked.connect(lambda checked=False, val=preset: self.speed_slider.setValue(val))
            layout.addWidget(pb)

        layout.addStretch()
        parent_layout.addWidget(sub)

    def _toggle_pause(self):
        self.sim_paused = not self.sim_paused
        if self.sim_paused:
            self.btn_pause.setText("▶ Resume")
            self.btn_pause.setStyleSheet(
                "background: #14532d; border: 1px solid #22c55e; color: #4ade80;"
                "padding: 4px 10px; border-radius: 4px; font-weight: bold; font-size: 11px;"
            )
            self._set_status("Simulation PAUSED.")
        else:
            self.btn_pause.setText("⏸ Pause")
            self.btn_pause.setStyleSheet(
                "background: #1e293b; border: 1px solid #f59e0b; color: #fbbf24;"
                "padding: 4px 10px; border-radius: 4px; font-weight: bold; font-size: 11px;"
            )
            self._set_status(f"Simulation RUNNING at {int(self.sim_speed)}x speed.")

    def _on_speed_slider_changed(self, val: int):
        self.sim_speed = float(val)
        self.speed_val_lbl.setText(f"{val}x")

    def _make_kpi(self, layout, title, val, color):
        card = QFrame()
        card.setMinimumWidth(140)
        card.setStyleSheet("background: #182030; border: 1px solid #2d3a52; border-radius: 6px;")
        vbox = QVBoxLayout(card)
        vbox.setContentsMargins(10, 4, 10, 4)
        t = QLabel(title)
        t.setStyleSheet("color: #94a3b8; font-size: 10px; font-weight: bold; border: none;")
        v = QLabel(val)
        v.setStyleSheet(f"color: {color}; font-size: 15px; font-weight: bold; border: none;")
        vbox.addWidget(t)
        vbox.addWidget(v)
        layout.addWidget(card)
        return v

    def _build_left_sidebar(self, parent_layout):
        self.sidebar_frame = QFrame()
        self.sidebar_frame.setFixedWidth(230)
        self.sidebar_frame.setStyleSheet("background-color: #121722; border-right: 1px solid #263044;")
        vbox = QVBoxLayout(self.sidebar_frame)
        vbox.setContentsMargins(10, 10, 10, 10)
        vbox.setSpacing(8)

        mode_hdr = QLabel("ROUTING & EDIT TOOLS")
        mode_hdr.setStyleSheet("color: #94a3b8; font-size: 11px; font-weight: bold; letter-spacing: 1px;")
        vbox.addWidget(mode_hdr)

        for label, mode in [("↖ Select / Edit Bends", "select"), ("━ Manual Pipe Router", "pipe")]:
            btn = QPushButton(label)
            btn.setCursor(Qt.PointingHandCursor)
            btn.setStyleSheet(
                "text-align: left; background: #0f172a; border: 1px solid #38bdf8;"
                "color: #38bdf8; padding: 8px 10px; border-radius: 5px; font-weight: bold;"
            )
            btn.clicked.connect(lambda checked=False, m=mode: self.scene.set_tool(m))
            vbox.addWidget(btn)

        drag_hdr = QLabel("DRAG & DROP SYMBOLS")
        drag_hdr.setStyleSheet("color: #94a3b8; font-size: 11px; font-weight: bold; letter-spacing: 1px; margin-top: 4px;")
        vbox.addWidget(drag_hdr)

        self.palette_list = ComponentPaletteList()
        vbox.addWidget(self.palette_list)

        import_btn = QPushButton("+ Import Custom Symbol")
        import_btn.setCursor(Qt.PointingHandCursor)
        import_btn.setStyleSheet(
            "background: #2e1065; border: 1px solid #a855f7; color: #e9d5ff;"
            "padding: 8px; border-radius: 5px; font-weight: bold;"
        )
        import_btn.clicked.connect(self._import_custom_symbol)
        vbox.addWidget(import_btn)

        del_btn = QPushButton("🗑 Delete Selected (Del)")
        del_btn.setCursor(Qt.PointingHandCursor)
        del_btn.setStyleSheet(
            "background: #451219; border: 1px solid #ef4444; color: #fca5a5;"
            "padding: 8px; border-radius: 5px; font-weight: bold;"
        )
        del_btn.clicked.connect(self._delete_selected)
        vbox.addWidget(del_btn)

        parent_layout.addWidget(self.sidebar_frame)

    def _import_custom_symbol(self):
        dlg = CustomSymbolDialog(self)
        if dlg.exec() == QDialog.Accepted:
            spec = dlg.get_symbol_spec()
            self.palette_list.register_custom_symbol(spec)
            self._set_dirty(True)
            self._set_status(f"Imported custom symbol '{spec['name']}'. Drag it from the left panel onto the grid.")

    def _delete_selected(self):
        if self.scene.read_only:
            return
        selected = self.scene.selectedItems()
        nodes = [i for i in selected if isinstance(i, PlumbingNodeItem)]
        pipes = [i for i in selected if isinstance(i, PipeEdgeItem)]
        if nodes or pipes:
            self.undo_stack.push(DeleteItemsCommand(self.scene, nodes, pipes))

    # ==========================================================================
    # PROJECT MANAGEMENT: NEW, OPEN, SAVE, SAVE AS & EXPORT PACKAGE
    # ==========================================================================
    def _serialize_project_data(self, include_live_telemetry: bool = False) -> dict:
        nodes_data, pipes_data = [], []
        for item in self.scene.items():
            if isinstance(item, PlumbingNodeItem):
                nd = {
                    "id": item.node_id,
                    "type": item.node_type,
                    "x": item.pos().x(),
                    "y": item.pos().y(),
                    "label": item.label,
                    "capacity": item.capacity,
                    "volume": item.volume,
                    "rated_flow": item.rated_flow,
                    "active": item.active,
                    "custom_spec": item.custom_spec
                }
                if include_live_telemetry:
                    nd["live_flow_m3h"] = round(item.current_flow, 3)
                    nd["totalizer_m3"] = round(item.totalizer_m3, 3)
                nodes_data.append(nd)
            elif isinstance(item, PipeEdgeItem):
                pd = {
                    "id": item.pipe_id,
                    "src": item.src_node.node_id,
                    "dst": item.dst_node.node_id,
                    "waypoints": [[p.x(), p.y()] for p in item.waypoints],
                    "diameter_mm": item.diameter_mm,
                    "color": item.flow_color.name()
                }
                if include_live_telemetry:
                    pd["live_flow_m3h"] = round(item.current_flow, 3)
                pipes_data.append(pd)

        payload = {
            "format_version": "2.0",
            "saved_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "author": f"{self.username} ({self.role})",
            "sim_speed": self.sim_speed,
            "custom_library": list(self.palette_list.custom_symbols.values()),
            "nodes": nodes_data,
            "pipes": pipes_data
        }
        if include_live_telemetry:
            payload["kpi_summary"] = {
                "total_inflow": self.kpi_inflow.text(),
                "total_demand": self.kpi_demand.text(),
                "stored_volume": self.kpi_stored.text(),
                "system_status": self.alarm_lbl.text()
            }
        return payload

    def _write_project_file(self, path: str, include_live_telemetry: bool = False) -> bool:
        try:
            data = self._serialize_project_data(include_live_telemetry=include_live_telemetry)
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            return True
        except Exception as exc:
            QMessageBox.critical(self, "Save Error", f"Failed to write project file:\n{exc}")
            return False

    def _new_project(self):
        if self.scene.read_only:
            QMessageBox.warning(self, "Permission Denied", "Only Admin users can create or edit projects.")
            return
        if not self._confirm_discard_unsaved():
            return

        self.scene.abort_current_action()
        self.scene.clear()
        self.undo_stack.clear()
        self.current_project_path = None
        self.view.reset_zoom()
        self.undo_stack.setClean()
        self._set_dirty(False)
        self._set_status("Created new blank SCADA project. Drag symbols from the left panel to begin.")

    def _reset_to_sample_plant(self):
        if not self._confirm_discard_unsaved():
            return
        self.scene.abort_current_action()
        self.scene.clear()
        self.undo_stack.clear()
        self.current_project_path = None
        self._load_default_plant()
        self._apply_role_permissions()
        self.view.fit_diagram()
        self.undo_stack.setClean()
        self._set_dirty(False)
        self._set_status("Loaded default Water Distribution Plant template.")

    def _open_project(self):
        if not self._confirm_discard_unsaved():
            return
        path, _ = QFileDialog.getOpenFileName(self, "Open SCADA Project", "", PROJECT_FILTER)
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)

            self.scene.abort_current_action()
            self.scene.clear()
            self.undo_stack.clear()

            if "sim_speed" in data:
                self.speed_slider.setValue(int(data["sim_speed"]))

            for spec in data.get("custom_library", []):
                if spec["symbol_id"] not in self.palette_list.custom_symbols:
                    self.palette_list.register_custom_symbol(spec)

            node_map = {}
            for nd in data.get("nodes", []):
                node = PlumbingNodeItem(
                    nd["id"], nd["type"], nd["x"], nd["y"], nd["label"],
                    nd["capacity"], nd["volume"], nd["rated_flow"], nd["active"],
                    custom_spec=nd.get("custom_spec")
                )
                if "totalizer_m3" in nd:
                    node.totalizer_m3 = float(nd["totalizer_m3"])
                self.scene.addItem(node)
                node_map[nd["id"]] = node

            for pd in data.get("pipes", []):
                if pd["src"] in node_map and pd["dst"] in node_map:
                    pipe = PipeEdgeItem(
                        pd["id"], node_map[pd["src"]], node_map[pd["dst"]],
                        pd.get("waypoints", []), pd.get("diameter_mm", 75), pd.get("color", "#06b6d4")
                    )
                    self.scene.addItem(pipe)

            self.current_project_path = path
            self._apply_role_permissions()
            self.view.fit_diagram()
            self.undo_stack.setClean()
            self._set_dirty(False)
            self._set_status(f"Opened project: {path}")
        except Exception as exc:
            QMessageBox.critical(self, "Open Project Error", f"Could not load project file:\n{exc}")

    def _save_project(self) -> bool:
        if not self.current_project_path:
            return self._save_project_as()
        if self._write_project_file(self.current_project_path, include_live_telemetry=False):
            self.undo_stack.setClean()
            self._set_dirty(False)
            self._set_status(f"Project saved: {self.current_project_path}")
            return True
        return False

    def _save_project_as(self) -> bool:
        default_name = os.path.basename(self.current_project_path) if self.current_project_path else "water_plant_project.scada"
        path, _ = QFileDialog.getSaveFileName(self, "Save SCADA Project As", default_name, PROJECT_FILTER)
        if not path:
            return False
        if not (path.lower().endswith(".scada") or path.lower().endswith(".json")):
            path += ".scada"
        if self._write_project_file(path, include_live_telemetry=False):
            self.current_project_path = path
            self.undo_stack.setClean()
            self._set_dirty(False)
            self._set_status(f"Project saved as: {path}")
            return True
        return False

    def _export_project_package(self):
        base_name = os.path.splitext(os.path.basename(self.current_project_path))[0] if self.current_project_path else "water_scada"
        path, _ = QFileDialog.getSaveFileName(
            self,
            "Export Standalone Project Package (.JSON)",
            f"{base_name}_export_{datetime.now().strftime('%Y%m%d_%H%M')}.json",
            "JSON Project Package (*.json)"
        )
        if not path:
            return
        if self._write_project_file(path, include_live_telemetry=True):
            self._set_status(f"Exported standalone project package with live telemetry to {path}")

    # ==========================================================================
    # EXPORT SUITE: PNG, PDF, CSV
    # ==========================================================================
    def _export_png(self):
        base_name = os.path.splitext(os.path.basename(self.current_project_path))[0] if self.current_project_path else "water_scada"
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Schematic as PNG", f"{base_name}_{datetime.now().strftime('%Y%m%d_%H%M')}.png", "PNG Image (*.png)"
        )
        if not path:
            return

        self.scene.clearSelection()
        bounds = self.scene.itemsBoundingRect().adjusted(-40, -40, 40, 40)
        if bounds.isEmpty():
            bounds = QRectF(0, 0, 1200, 700)

        scale = 2.0
        img = QImage(int(bounds.width() * scale), int(bounds.height() * scale), QImage.Format_ARGB32)
        img.fill(QColor("#0d111a"))

        painter = QPainter(img)
        painter.setRenderHint(QPainter.Antialiasing)
        self.scene.render(painter, QRectF(img.rect()), bounds)
        painter.end()

        img.save(path, "PNG")
        self._set_status(f"Exported high-resolution schematic PNG to {path}")

    def _export_pdf(self):
        base_name = os.path.splitext(os.path.basename(self.current_project_path))[0] if self.current_project_path else "water_pid"
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Engineering Drawing (PDF)", f"{base_name}_{datetime.now().strftime('%Y%m%d_%H%M')}.pdf", "PDF Document (*.pdf)"
        )
        if not path:
            return

        self.scene.clearSelection()
        writer = QPdfWriter(path)
        writer.setPageSize(QPageSize(QPageSize.A3))
        writer.setPageOrientation(QPageLayout.Landscape)
        writer.setResolution(300)

        painter = QPainter(writer)
        painter.setRenderHint(QPainter.Antialiasing)

        page_rect = painter.viewport()
        margin = 100
        title_block_h = 260
        diagram_rect = QRectF(
            margin, margin,
            page_rect.width() - 2 * margin,
            page_rect.height() - 2 * margin - title_block_h
        )

        bounds = self.scene.itemsBoundingRect().adjusted(-40, -40, 40, 40)
        if bounds.isEmpty():
            bounds = QRectF(0, 0, 1200, 700)
        self.scene.render(painter, diagram_rect, bounds, Qt.KeepAspectRatio)

        tb_rect = QRectF(margin, diagram_rect.bottom() + 30, page_rect.width() - 2 * margin, title_block_h - 30)
        painter.setPen(QPen(QColor("#1e293b"), 6))
        painter.setBrush(QBrush(QColor("#f8fafc")))
        painter.drawRect(tb_rect)

        proj_label = os.path.basename(self.current_project_path) if self.current_project_path else "Untitled_Plant.scada"
        painter.setPen(QColor("#0f172a"))
        painter.setFont(QFont("Segoe UI", 14, QFont.Bold))
        painter.drawText(
            tb_rect.adjusted(40, 25, -40, -20),
            Qt.AlignLeft | Qt.AlignTop,
            f"2D WATER DISTRIBUTION SCADA & P&ID SCHEMATIC — PROJECT: {proj_label}"
        )

        painter.setFont(QFont("Consolas", 10))
        meta = (
            f"Generated By: {self.username} ({self.role})    |    "
            f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}    |    "
            f"Inflow: {self.kpi_inflow.text()}    |    "
            f"Demand: {self.kpi_demand.text()}    |    "
            f"Stored: {self.kpi_stored.text()}"
        )
        painter.drawText(
            tb_rect.adjusted(40, 115, -40, -20),
            Qt.AlignLeft | Qt.AlignTop,
            meta
        )

        painter.end()
        self._set_status(f"Exported engineering PDF drawing to {path}")

    def _export_csv(self):
        base_name = os.path.splitext(os.path.basename(self.current_project_path))[0] if self.current_project_path else "scada_telemetry"
        path, _ = QFileDialog.getSaveFileName(
            self, "Export Telemetry & Meter Log (CSV)", f"{base_name}_{datetime.now().strftime('%Y%m%d_%H%M')}.csv", "CSV Spreadsheet (*.csv)"
        )
        if not path:
            return

        nodes = [i for i in self.scene.items() if isinstance(i, PlumbingNodeItem)]
        pipes = [i for i in self.scene.items() if isinstance(i, PipeEdgeItem)]

        with open(path, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["Project File", os.path.basename(self.current_project_path) if self.current_project_path else "Untitled_Plant.scada"])
            writer.writerow(["Timestamp", datetime.now().strftime("%Y-%m-%d %H:%M:%S")])
            writer.writerow(["Operator", f"{self.username} ({self.role})"])
            writer.writerow(["Total Inflow", self.kpi_inflow.text(), "Total Demand", self.kpi_demand.text(), "Stored Volume", self.kpi_stored.text()])
            writer.writerow([])

            writer.writerow(["EQUIPMENT TELEMETRY"])
            writer.writerow(["Tag / Name", "Type", "State", "Current Flow (m3/h)", "Rated Flow (m3/h)", "Volume (m3)", "Capacity (m3)", "Fill (%)", "Totalizer Reading (m3)"])
            for n in nodes:
                pct = f"{(n.volume / n.capacity * 100):.1f}%" if n.node_type == "tank" and n.capacity > 0 else "-"
                vol_str = f"{n.volume:.2f}" if n.node_type == "tank" else "-"
                cap_str = f"{n.capacity:.2f}" if n.node_type == "tank" else "-"
                tot_str = f"{n.totalizer_m3:.3f}" if n.node_type == "meter" else "-"
                state_str = "ACTIVE/OPEN" if n.active else "STOPPED/SHUT"
                writer.writerow([
                    n.label, n.node_type.upper(), state_str,
                    f"{n.current_flow:.2f}", f"{n.rated_flow:.2f}",
                    vol_str, cap_str, pct, tot_str
                ])

            writer.writerow([])
            writer.writerow(["PIPELINE FLOWS"])
            writer.writerow(["Pipe ID", "From", "To", "Diameter (mm)", "Flow Rate (m3/h)"])
            for p in pipes:
                writer.writerow([p.pipe_id, p.src_node.label, p.dst_node.label, p.diameter_mm, f"{p.current_flow:.2f}"])

        self._set_status(f"Exported telemetry & meter log CSV to {path}")

    # ==========================================================================
    # HYDRAULIC & MASS-BALANCE SOLVER
    # ==========================================================================
    def _step_simulation(self):
        if self.sim_paused:
            return

        dt_sec = 0.05
        dt_hours = (dt_sec * self.sim_speed) / 3600.0

        nodes = [i for i in self.scene.items() if isinstance(i, PlumbingNodeItem)]
        pipes = [i for i in self.scene.items() if isinstance(i, PipeEdgeItem)]

        for n in nodes:
            n.current_flow = 0.0
            n.alarm = False
        for p in pipes:
            p.current_flow = 0.0

        in_pipes = {n.node_id: [] for n in nodes}
        out_pipes = {n.node_id: [] for n in nodes}
        for p in pipes:
            out_pipes[p.src_node.node_id].append(p)
            in_pipes[p.dst_node.node_id].append(p)

        for _ in range(6):
            for n in nodes:
                incoming_q = sum(p.current_flow for p in in_pipes[n.node_id])
                outgoing = out_pipes[n.node_id]

                if n.node_type == "source":
                    n.current_flow = n.rated_flow
                    if outgoing:
                        share = n.current_flow / len(outgoing)
                        for p in outgoing:
                            if p.dst_node.node_type == "tank" and p.dst_node.volume >= p.dst_node.capacity:
                                p.current_flow = 0.0
                            else:
                                p.current_flow = share

                elif n.node_type == "valve":
                    n.current_flow = incoming_q if n.active else 0.0
                    if outgoing:
                        share = n.current_flow / len(outgoing)
                        for p in outgoing:
                            p.current_flow = share

                elif n.node_type == "check_valve":
                    n.current_flow = max(0.0, incoming_q)
                    if outgoing:
                        share = n.current_flow / len(outgoing)
                        for p in outgoing:
                            p.current_flow = share

                elif n.node_type == "meter":
                    n.current_flow = incoming_q
                    if outgoing:
                        share = n.current_flow / len(outgoing)
                        for p in outgoing:
                            p.current_flow = share

                elif n.node_type == "motor":
                    can_pump = n.active
                    upstream_tanks = [p.src_node for p in in_pipes[n.node_id] if p.src_node.node_type == "tank"]
                    for ut in upstream_tanks:
                        if ut.volume <= ut.capacity * 0.10:
                            can_pump = False
                            n.active = False

                    if can_pump and outgoing:
                        avail = n.rated_flow if upstream_tanks else min(n.rated_flow, incoming_q)
                        n.current_flow = avail
                        if upstream_tanks and in_pipes[n.node_id]:
                            in_share = avail / len(in_pipes[n.node_id])
                            for ip in in_pipes[n.node_id]:
                                ip.current_flow = in_share
                        out_share = avail / len(outgoing)
                        for op in outgoing:
                            if op.dst_node.node_type == "tank" and op.dst_node.volume >= op.dst_node.capacity:
                                op.current_flow = 0.0
                            else:
                                op.current_flow = out_share
                    else:
                        n.current_flow = 0.0
                        for op in outgoing:
                            op.current_flow = 0.0

                elif n.node_type == "header":
                    n.current_flow = incoming_q
                    if outgoing:
                        total_req = sum(
                            p.dst_node.rated_flow if p.dst_node.node_type == "demand" else 20.0
                            for p in outgoing
                        )
                        for p in outgoing:
                            req = p.dst_node.rated_flow if p.dst_node.node_type == "demand" else 20.0
                            p.current_flow = incoming_q * (req / max(1.0, total_req))

                elif n.node_type == "demand":
                    n.current_flow = min(n.rated_flow, incoming_q)

        total_inflow = 0.0
        total_demand = 0.0
        total_vol = 0.0
        total_cap = 0.0
        alarm_msgs = []

        for n in nodes:
            if n.node_type == "source":
                total_inflow += sum(p.current_flow for p in out_pipes[n.node_id])
            elif n.node_type == "demand":
                total_demand += n.current_flow
            elif n.node_type == "meter":
                n.totalizer_m3 += n.current_flow * dt_hours
            elif n.node_type == "tank":
                q_in = sum(p.current_flow for p in in_pipes[n.node_id])
                q_out = sum(p.current_flow for p in out_pipes[n.node_id])
                n.volume = max(0.0, min(n.capacity, n.volume + (q_in - q_out) * dt_hours))
                total_vol += n.volume
                total_cap += n.capacity
                if n.volume < n.capacity * 0.15:
                    n.alarm = True
                    alarm_msgs.append(f"Low Level: {n.label}")
            n.advance_animation(not self.sim_paused)
            n.update()

        anim_factor = max(0.4, min(2.5, self.sim_speed / 15.0))
        for p in pipes:
            p.advance_flow(dt_sec, anim_factor)

        self.kpi_inflow.setText(f"{total_inflow:.1f} m³/h")
        self.kpi_demand.setText(f"{total_demand:.1f} m³/h")
        self.kpi_stored.setText(f"{total_vol:.1f} / {total_cap:.0f} m³")

        if alarm_msgs:
            self.alarm_lbl.setText("⚠ " + " | ".join(alarm_msgs[:2]))
            self.alarm_lbl.setStyleSheet(
                "background: #451219; border: 1px solid #ef4444; color: #fca5a5;"
                "border-radius: 6px; padding: 8px 12px; font-weight: bold;"
            )
        else:
            self.alarm_lbl.setText("● SYSTEM NORMAL")
            self.alarm_lbl.setStyleSheet(
                "background: #132a1c; border: 1px solid #22c55e; color: #4ade80;"
                "border-radius: 6px; padding: 8px 12px; font-weight: bold;"
            )

    def _load_default_plant(self):
        src1 = PlumbingNodeItem("s1", "source", 30, 180, "City Water 01", rated_flow=35.0)
        vlv1 = PlumbingNodeItem("v1", "valve", 180, 178, "Inlet Valve", active=True)
        mtr1 = PlumbingNodeItem("m1", "meter", 270, 175, "Main Meter")
        sump1 = PlumbingNodeItem("t1", "tank", 390, 150, "Sump 1", capacity=40.0, volume=28.0)

        pmp1 = PlumbingNodeItem("p1", "motor", 540, 175, "Transfer Pump", rated_flow=45.0, active=True)
        nrv1 = PlumbingNodeItem("c1", "check_valve", 660, 180, "Check Valve")
        main_t = PlumbingNodeItem("t2", "tank", 750, 150, "Main Tank", capacity=38.0, volume=24.0)

        pmp2 = PlumbingNodeItem("p2", "motor", 900, 175, "Booster Pump", rated_flow=50.0, active=True)
        hdr = PlumbingNodeItem("h1", "header", 1020, 173, "Dist. Header")

        d1 = PlumbingNodeItem("d1", "demand", 1230, 90, "Kitchen & Drink", rated_flow=15.0)
        d2 = PlumbingNodeItem("d2", "demand", 1230, 240, "Production Line", rated_flow=35.0)

        for n in (src1, vlv1, mtr1, sump1, pmp1, nrv1, main_t, pmp2, hdr, d1, d2):
            self.scene.addItem(n)

        connections = [
            (src1, vlv1, [], 75, "#06b6d4"),
            (vlv1, mtr1, [], 75, "#06b6d4"),
            (mtr1, sump1, [], 75, "#06b6d4"),
            (sump1, pmp1, [], 110, "#eab308"),
            (pmp1, nrv1, [], 110, "#eab308"),
            (nrv1, main_t, [], 110, "#eab308"),
            (main_t, pmp2, [], 160, "#eab308"),
            (pmp2, hdr, [], 160, "#eab308"),
            (hdr, d1, [(1200, 205), (1200, 117)], 63, "#ec4899"),
            (hdr, d2, [(1200, 205), (1200, 267)], 75, "#ec4899"),
        ]
        for s, d, wp, dia, col in connections:
            self.scene.addItem(PipeEdgeItem(str(uuid.uuid4())[:8], s, d, wp, dia, col))


if __name__ == "__main__":
    app = QApplication(sys.argv)
    auth = AuthManager()
    login = LoginDialog(auth)
    if login.exec() == QDialog.Accepted:
        win = WaterScadaStudio(login.authenticated_user, login.authenticated_role, auth)
        win.show()
        sys.exit(app.exec())