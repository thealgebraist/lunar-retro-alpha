import http.server
import socketserver
import sys

PORT = 8000

class WasmHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        # Allow cross-origin for local dev if needed
        self.send_header('Access-Control-Allow-Origin', '*')
        super().end_headers()

Handler = WasmHandler
Handler.extensions_map.update({
    '.wasm': 'application/wasm',
    '.html': 'text/html',
    '.js': 'application/javascript',
})

socketserver.TCPServer.allow_reuse_address = True
try:
    with socketserver.TCPServer(("", PORT), Handler) as httpd:
        print(f"Serving Lunar Retro-Alpha at http://localhost:{PORT}")
        print("Press Ctrl+C to stop.")
        httpd.serve_forever()
except KeyboardInterrupt:
    print("\nShutting down server.")
    sys.exit(0)
except Exception as e:
    print(f"Error: {e}")
    sys.exit(1)