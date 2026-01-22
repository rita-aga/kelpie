"""
Session management for VerificationFS

Handles session lifecycle, tracking active sessions, and cleanup.
"""

import uuid
from typing import Optional

from .wrapper import VerificationFS


class SessionManager:
    """
    Manage VerificationFS sessions.

    Provides:
    - Session creation with unique IDs
    - Active session tracking
    - Session resumption
    - Cleanup
    """

    def __init__(self, project_root: str):
        """
        Initialize session manager.

        Args:
            project_root: Path to project root
        """
        self.project_root = project_root
        self._active_session: Optional[VerificationFS] = None
        self._session_id: Optional[str] = None

    def generate_session_id(self) -> str:
        """
        Generate a unique session ID.

        Returns:
            Session ID (short hex string)
        """
        return uuid.uuid4().hex[:12]

    async def init_session(self, task: str, session_id: Optional[str] = None) -> VerificationFS:
        """
        Initialize a new session or resume existing one.

        Args:
            task: Task description
            session_id: Existing session ID (if resuming), or None for new

        Returns:
            VerificationFS instance
        """
        if not session_id:
            session_id = self.generate_session_id()

        self._session_id = session_id

        # Open VerificationFS (creates or resumes session)
        vfs = await VerificationFS.open(session_id, task, self.project_root).__aenter__()
        self._active_session = vfs

        return vfs

    def get_active_session(self) -> Optional[VerificationFS]:
        """
        Get the currently active session.

        Returns:
            Active VerificationFS instance or None
        """
        return self._active_session

    def get_session_id(self) -> Optional[str]:
        """
        Get the current session ID.

        Returns:
            Session ID or None
        """
        return self._session_id

    async def close_session(self):
        """Close the active session."""
        if self._active_session:
            await self._active_session.afs.close()
            self._active_session = None
            self._session_id = None
