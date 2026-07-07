FROM python:3.12-slim

WORKDIR /app
COPY server.py index.html ./

# 대부분의 PaaS(Render/Railway/Fly 등)는 PORT 환경변수를 주입합니다.
ENV PORT=8080
EXPOSE 8080

CMD ["python", "server.py"]
