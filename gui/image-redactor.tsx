"use client"

import type React from "react"
import { useState, useRef, useEffect } from "react"
import { Button } from "@/components/ui/button"

const ImageRedactor: React.FC = () => {
  const [image, setImage] = useState<HTMLImageElement | null>(null)
  const [selectedBlocks, setSelectedBlocks] = useState<boolean[][]>([])
  const canvasRef = useRef<HTMLCanvasElement>(null)

  const BLOCK_SIZE = 32

  useEffect(() => {
    if (image && canvasRef.current) {
      const canvas = canvasRef.current
      const ctx = canvas.getContext("2d")
      if (ctx) {
        canvas.width = image.width
        canvas.height = image.height
        ctx.drawImage(image, 0, 0)

        // Initialize selectedBlocks
        const blocksX = Math.ceil(image.width / BLOCK_SIZE)
        const blocksY = Math.ceil(image.height / BLOCK_SIZE)
        setSelectedBlocks(
          Array(blocksY)
            .fill(null)
            .map(() => Array(blocksX).fill(false)),
        )
      }
    }
  }, [image])

  const handleImageUpload = (e: React.ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0]
    if (file) {
      const reader = new FileReader()
      reader.onload = (event) => {
        const img = new Image()
        img.onload = () => setImage(img)
        img.src = event.target?.result as string
      }
      reader.readAsDataURL(file)
    }
  }

  const handleCanvasClick = (e: React.MouseEvent<HTMLCanvasElement>) => {
    if (canvasRef.current && image) {
      const rect = canvasRef.current.getBoundingClientRect()
      const x = Math.floor((e.clientX - rect.left) / BLOCK_SIZE)
      const y = Math.floor((e.clientY - rect.top) / BLOCK_SIZE)

      setSelectedBlocks((prev) => {
        const newBlocks = [...prev]
        newBlocks[y][x] = !newBlocks[y][x]
        return newBlocks
      })

      const ctx = canvasRef.current.getContext("2d")
      if (ctx) {
        if (!selectedBlocks[y][x]) {
          ctx.fillStyle = "black"
          ctx.fillRect(x * BLOCK_SIZE, y * BLOCK_SIZE, BLOCK_SIZE, BLOCK_SIZE)
        } else {
          ctx.drawImage(
            image,
            x * BLOCK_SIZE,
            y * BLOCK_SIZE,
            BLOCK_SIZE,
            BLOCK_SIZE,
            x * BLOCK_SIZE,
            y * BLOCK_SIZE,
            BLOCK_SIZE,
            BLOCK_SIZE,
          )
        }
      }
    }
  }

  const handleDownload = () => {
    if (canvasRef.current) {
      // Download redacted image
      const link = document.createElement("a")
      link.download = "redacted_image.png"
      link.href = canvasRef.current.toDataURL()
      link.click()

      // Download JSON file
      const jsonContent = JSON.stringify(selectedBlocks)
      const blob = new Blob([jsonContent], { type: "application/json" })
      const url = URL.createObjectURL(blob)
      const jsonLink = document.createElement("a")
      jsonLink.download = "selected_blocks.json"
      jsonLink.href = url
      jsonLink.click()
      URL.revokeObjectURL(url)
    }
  }

  return (
    <div className="flex flex-col items-center justify-center min-h-screen bg-gray-100 p-4">
      <input type="file" accept="image/*" onChange={handleImageUpload} className="mb-4" />
      {image && (
        <>
          <canvas
            ref={canvasRef}
            onClick={handleCanvasClick}
            style={{ border: "1px solid black", cursor: "pointer" }}
            className="mb-4"
          />
          <Button onClick={handleDownload}>Download Redacted Image and JSON</Button>
        </>
      )}
    </div>
  )
}

export default ImageRedactor

